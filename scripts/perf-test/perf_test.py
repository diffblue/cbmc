#!/usr/bin/env python

from __future__ import print_function

import argparse
import boto3
import concurrent.futures
import contextlib
import datetime
import json
import logging
import os
import re
import shutil
import sys
import tempfile
import time
import urllib


@contextlib.contextmanager
def make_temp_directory():
    """
    create a temporary directory and remove it once the statement completes
    """
    temp_dir = tempfile.mkdtemp()
    try:
        yield temp_dir
    finally:
        shutil.rmtree(temp_dir)


def same_dir(filename):
    d = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(d, filename)


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('-r', '--repository', type=str, required=True,
                        help='CodeCommit or GitHub repository containing ' +
                             'code to evaluate')
    parser.add_argument('-c', '--commit-id', type=str, required=True,
                        help='git revision to evaluate')
    parser.add_argument('-e', '--email', type=str, required=True,
                        help='Email address to notify about results')
    parser.add_argument('-t', '--instance-type', type=str,
                        default='r4.16xlarge',
                        help='Amazon EC2 instance type to use ' +
                             '(default: r4.16xlarge)')
    parser.add_argument('-m', '--mode',
                        choices=['spot', 'on-demand', 'batch'],
                        default='spot',
                        help='Choose fleet to run benchmarks on ' +
                             '(default: Amazon EC2 Spot fleet)')
    parser.add_argument('-R', '--region', type=str,
                        help='Set fixed region instead of cheapest fleet')
    parser.add_argument('-j', '--parallel', type=int, default=4,
                        help='Fleet size of concurrently running hosts ' +
                             '(default: 4)')
    parser.add_argument('-k', '--ssh-key-name', type=str, default='',
                        help='EC2 key name for SSH access to fleet')
    parser.add_argument('-K', '--ssh-key', type=str,
                        help='SSH public key file for access to fleet ' +
                             '(requires -K/--ssh-key-name)')
    parser.add_argument('-T', '--tasks', type=str,
                        default='quick',
                        help='Subset of tasks to run (quick, full; ' +
                             'default: quick; or regex of SV-COMP task(s))')
    parser.add_argument('-B', '--build', type=str,
                        default=same_dir('build.yaml'),
                        help='Non-default build template to use')
    parser.add_argument('-W', '--witness-check', action='store_true',
                        help='Run witness checks after benchmarking')
    parser.add_argument('-C', '--compare-to', default=[], action='append',
                        help='Include past results in tables [may repeat]')
    parser.add_argument('-P', '--use-perf', action='store_true',
                        help='Use Linux Perf for profiling')

    args = parser.parse_args()

    assert(args.repository.startswith('https://github.com/') or
           args.repository.startswith('https://git-codecommit.'))
    assert(not args.ssh_key or args.ssh_key_name)
    if args.ssh_key:
        assert(os.path.isfile(args.ssh_key))
    assert(os.path.isfile(args.build))

    return args


def prepare_s3(session, bucket_name, artifact_uploaded_arn):
    # create a bucket for storing artifacts
    logger = logging.getLogger('perf_test')
    s3 = session.resource('s3', region_name='us-east-1')
    buckets = list(s3.buckets.all())

    for b in buckets:
        if b.name == bucket_name:
            logger.info('us-east-1: S3 bucket {} exists'.format(bucket_name))
            return

    cfn = session.resource('cloudformation', region_name='us-east-1')
    with open(same_dir('s3.yaml')) as f:
        CFN_s3 = f.read()
    cfn.create_stack(
        StackName='perf-test-s3',
        TemplateBody=CFN_s3,
        Parameters=[
            {
                'ParameterKey': 'SnsTopicArn',
                'ParameterValue': artifact_uploaded_arn
            },
            {
                'ParameterKey': 'S3BucketName',
                'ParameterValue': bucket_name
            }
        ])

    waiter = cfn.meta.client.get_waiter('stack_create_complete')
    waiter.wait(StackName='perf-test-s3', WaiterConfig={'Delay': 10})
    logger.info('us-east-1: S3 bucket {} set up'.format(bucket_name))


def prepare_sns_s3(session, email, bucket_name):
    # create instance_terminated topic
    # create artifact_uploaded topic
    logger = logging.getLogger('perf_test')
    sns = session.resource('sns', region_name='us-east-1')
    topics = list(sns.topics.all())
    instance_terminated_arn = None
    artifact_uploaded_arn = None

    for t in topics:
        if t.attributes['DisplayName'] == 'instance_terminated':
            instance_terminated_arn = t.arn
            logger.info('us-east-1: SNS topic instance_terminated exists')
            if int(t.attributes['SubscriptionsPending']) > 0:
                logger.warning('us-east-1: SNS topic instance_terminated ' +
                               'has pending subscription confirmations')
        elif t.attributes['DisplayName'] == 'artifact_uploaded':
            artifact_uploaded_arn = t.arn
            logger.info('us-east-1: SNS topic artifact_uploaded exists')
            if int(t.attributes['SubscriptionsPending']) > 0:
                logger.warning('us-east-1: SNS topic artifact_uploaded ' +
                               'has pending subscription confirmations')

    cfn = session.resource('cloudformation', region_name='us-east-1')

    with open(same_dir('sns.yaml')) as f:
        CFN_sns = f.read()

    if not instance_terminated_arn:
        cfn.create_stack(
                StackName='perf-test-sns-instance-term',
                TemplateBody=CFN_sns,
                Parameters=[
                    {
                        'ParameterKey': 'NotificationAddress',
                        'ParameterValue': email
                    },
                    {
                        'ParameterKey': 'SnsTopicName',
                        'ParameterValue': 'instance_terminated'
                    }
                ])

    if not artifact_uploaded_arn:
        cfn.create_stack(
                StackName='perf-test-sns-artifact-uploaded',
                TemplateBody=CFN_sns,
                Parameters=[
                    {
                        'ParameterKey': 'NotificationAddress',
                        'ParameterValue': email
                    },
                    {
                        'ParameterKey': 'SnsTopicName',
                        'ParameterValue': 'artifact_uploaded'
                    }
                ])

    waiter = cfn.meta.client.get_waiter('stack_create_complete')
    if not instance_terminated_arn:
        waiter.wait(
                StackName='perf-test-sns-instance-term',
                WaiterConfig={'Delay': 10})
        stack = cfn.Stack('perf-test-sns-instance-term')
        instance_terminated_arn = stack.outputs[0]['OutputValue']
        logger.info('us-east-1: SNS topic instance_terminated set up')
    if not artifact_uploaded_arn:
        waiter.wait(
                StackName='perf-test-sns-artifact-uploaded',
                WaiterConfig={'Delay': 10})
        stack = cfn.Stack('perf-test-sns-artifact-uploaded')
        artifact_uploaded_arn = stack.outputs[0]['OutputValue']
        logger.info('us-east-1: SNS topic artifact_uploaded set up')

    prepare_s3(session, bucket_name, artifact_uploaded_arn)
    s3 = session.client('s3', region_name='us-east-1')
    s3.upload_file(
            Bucket=bucket_name,
            Key='ec2-terminate.sh',
            Filename=same_dir('ec2-terminate.sh'))
    s3.upload_file(
            Bucket=bucket_name,
            Key='run-on-ec2.sh',
            Filename=same_dir('run-on-ec2.sh'))

    return instance_terminated_arn


def get_default_vpc(session, region, az):
    # find the id of the default VPC in the chosen region
    logger = logging.getLogger('perf_test')

    ec2 = session.client('ec2', region_name=region)

    res = ec2.describe_vpcs(Filters=[{'Name': 'isDefault', 'Values': ['true']}])
    vpc = res['Vpcs'][0]['VpcId']
    logger.info(region + ': default VPC: ' + vpc)

    res = ec2.describe_subnets(
            Filters=[
                {'Name': 'vpc-id', 'Values': [vpc]},
                {'Name': 'default-for-az', 'Values': ['true']}
            ])
    subnets = ','.join(s['SubnetId'] for s in res['Subnets'])
    logger.info(region + ': default subnets: ' + subnets)

    res = ec2.describe_subnets(
            Filters=[
                {'Name': 'vpc-id', 'Values': [vpc]},
                {'Name': 'availability-zone', 'Values': [az]},
                {'Name': 'default-for-az', 'Values': ['true']}
            ])
    subnet_for_az = res['Subnets'][0]['SubnetId']
    logger.info(region + ': default subnet for ' + az + ': ' + subnet_for_az)

    return (vpc, subnets, subnet_for_az)


def select_region(session, mode, region, instance_type):
    # find the region and az with the lowest spot price for the chosen instance
    # type
    # based on https://gist.github.com/pahud/fbbc1fd80fac4544fd0a3a480602404e
    logger = logging.getLogger('perf_test')

    if not region:
        ec2 = session.client('ec2')
        regions = [r['RegionName'] for r in ec2.describe_regions()['Regions']]
    else:
        regions = [region]

    min_region = None
    min_az = None
    min_price = None

    if mode == 'on-demand':
        logger.info('global: Fetching on-demand prices for ' + instance_type)
        with make_temp_directory() as tmp_dir:
            for r in regions:
                json_file = os.path.join(tmp_dir, 'index.json')
                urllib.request.urlretrieve(
                        'https://pricing.us-east-1.amazonaws.com/offers/' +
                        'v1.0/aws/AmazonEC2/current/' + r + '/index.json',
                        json_file)
                with open(json_file) as jf:
                    json_result = json.load(jf)
                key = None
                for p in json_result['products']:
                    v = json_result['products'][p]
                    a = v['attributes']
                    if ((v['productFamily'] == 'Compute Instance') and
                            (a['instanceType'] == instance_type) and
                            (a['tenancy'] == 'Shared') and
                            (a['operatingSystem'] == 'Linux')):
                        assert(not key)
                        key = p
                for c in json_result['terms']['OnDemand'][key]:
                    v = json_result['terms']['OnDemand'][key][c]
                    for p in v['priceDimensions']:
                        price = v['priceDimensions'][p]['pricePerUnit']['USD']
                if min_region is None or float(price) < min_price:
                    min_region = r
                    ec2 = session.client('ec2', region_name=r)
                    azs = ec2.describe_availability_zones(
                            Filters=[{'Name': 'region-name', 'Values': [r]}])
                    min_az = azs['AvailabilityZones'][0]['ZoneName']
                    min_price = float(price)

        logger.info('global: Lowest on-demand price: {} ({}): {}'.format(
            min_region, min_az, min_price))
    else:
        logger.info('global: Fetching spot prices for ' + instance_type)
        for r in regions:
            ec2 = session.client('ec2', region_name=r)
            res = ec2.describe_spot_price_history(
                    InstanceTypes=[instance_type],
                    ProductDescriptions=['Linux/UNIX (Amazon VPC)'],
                    StartTime=datetime.datetime.now())
            history = res['SpotPriceHistory']
            for az in history:
                if min_region is None or float(az['SpotPrice']) < min_price:
                    min_region = r
                    min_az = az['AvailabilityZone']
                    min_price = float(az['SpotPrice'])

        logger.info('global: Lowest spot price: {} ({}): {}'.format(
            min_region, min_az, min_price))

    # https://cloud-images.ubuntu.com/locator/ec2/
    # 20201120 - Ubuntu 20.04 LTS (focal) - hvm:ebs-ssd
    AMI_ids = {
        "Mappings": {
            "RegionMap": {
		"af-south-1": { "64": "ami-0196a23f828d6e619" },
		"ap-east-1": { "64": "ami-f6511c87" },
		"ap-northeast-1": { "64": "ami-0e40a27db137d33cb" },
		"ap-northeast-2": { "64": "ami-01ff1255cee8004b8" },
		"ap-northeast-3": { "64": "ami-0b58a665b8d0d720c" },
		"ap-south-1": { "64": "ami-0cecfffd8cae9481c" },
		"ap-southeast-1": { "64": "ami-0dbb8181cd0ce9cff" },
		"ap-southeast-2": { "64": "ami-0f150e4544fb95045" },
		"ca-central-1": { "64": "ami-03060448f5c8f2199" },
		"cn-north-1": { "64": "ami-00cc446c1f9e0b72a" },
		"cn-northwest-1": { "64": "ami-05b363127143238ba" },
		"eu-central-1": { "64": "ami-09f14afb2e15caab5" },
		"eu-north-1": { "64": "ami-01450210d4ebb3bab" },
		"eu-south-1": { "64": "ami-0e3c0649c89ccddc9" },
		"eu-west-1": { "64": "ami-048309a44dad514df" },
		"eu-west-2": { "64": "ami-099ae17a6a688b1cc" },
		"eu-west-3": { "64": "ami-098efdd0afb686fd5" },
		"me-south-1": { "64": "ami-098b94183f8e74ecc" },
		"sa-east-1": { "64": "ami-0cc03bf224d6eb2fc" },
		"us-east-1": { "64": "ami-08306577a6694f5e7" },
		"us-east-2": { "64": "ami-0be9fcdb56a1f1226" },
		"us-west-1": { "64": "ami-04d12df4da18327bd" },
		"us-west-2": { "64": "ami-082e4f383a98efbe9" },
            }
        }
    }

    ami = AMI_ids['Mappings']['RegionMap'][min_region]['64']

    return (min_region, min_az, min_price, ami)


def prepare_ebs(session, region, az, ami, ssh_key_name):
    # create an ebs volume that contains the benchmark sources
    logger = logging.getLogger('perf_test')
    ec2 = session.client('ec2', region_name=region)
    snapshots = ec2.describe_snapshots(
            OwnerIds=['self'],
            Filters=[
                {
                    'Name': 'tag:Name',
                    'Values': ['perf-test-base']
                }
            ])

    if snapshots['Snapshots']:
        logger.info(region + ': EBS snapshot exists')
    else:
        logger.info(region + ': EBS snapshot preparation required')
        cfn = session.resource('cloudformation', region_name=region)
        with open(same_dir('ebs.yaml')) as f:
            CFN_ebs = f.read()
        stack = cfn.create_stack(
                StackName='perf-test-build-ebs',
                TemplateBody=CFN_ebs,
                Parameters=[
                    {
                        'ParameterKey': 'Ami',
                        'ParameterValue': ami
                    },
                    {
                        'ParameterKey': 'AvailabilityZone',
                        'ParameterValue': az
                    },
                    {
                        'ParameterKey': 'SSHKeyName',
                        'ParameterValue': ssh_key_name
                    }
                ])

        waiter = cfn.meta.client.get_waiter('stack_create_complete')
        waiter.wait(StackName='perf-test-build-ebs')
        instance_id = stack.outputs[0]['OutputValue']
        logger.info(region + ': Waiting for EBS snapshot preparation on ' +
                    instance_id)
        waiter = ec2.get_waiter('instance_stopped')
        waiter.wait(
                InstanceIds=[instance_id],
                WaiterConfig={
                    'Delay': 30,
                    'MaxAttempts': 120
                })
        stack.delete()
        waiter = cfn.meta.client.get_waiter('stack_delete_complete')
        waiter.wait(StackName='perf-test-build-ebs')
        logger.info(region + ': EBS snapshot prepared')

        snapshots = ec2.describe_snapshots(
                OwnerIds=['self'],
                Filters=[
                    {
                        'Name': 'tag:Name',
                        'Values': ['perf-test-base']
                    }
                ])

    return snapshots['Snapshots'][0]['SnapshotId']


def build(session, region, ami, subnet, repository, commit_id, bucket_name,
        perf_test_id, build_file, use_perf):
    # build the chosen commit
    logger = logging.getLogger('perf_test')

    cfn = session.resource('cloudformation', region_name=region)
    with open(build_file) as f:
        CFN_build = f.read()
    stack_name = 'perf-test-build-' + perf_test_id
    stack = cfn.create_stack(
            StackName=stack_name,
            TemplateBody=CFN_build,
            Parameters=[
                {
                    'ParameterKey': 'Ami',
                    'ParameterValue': ami
                },
                {
                    'ParameterKey': 'S3Bucket',
                    'ParameterValue': bucket_name
                },
                {
                    'ParameterKey': 'Subnet',
                    'ParameterValue': subnet
                },
                {
                    'ParameterKey': 'PerfTestId',
                    'ParameterValue': perf_test_id
                },
                {
                    'ParameterKey': 'Repository',
                    'ParameterValue': repository
                },
                {
                    'ParameterKey': 'CommitId',
                    'ParameterValue': commit_id
                },
                {
                    'ParameterKey': 'UsePerf',
                    'ParameterValue': str(use_perf)
                },
            ],
            Capabilities=['CAPABILITY_NAMED_IAM'])

    waiter = cfn.meta.client.get_waiter('stack_create_complete')
    waiter.wait(StackName=stack_name)
    release_instance_id = stack.outputs[0]['OutputValue']
    profiling_instance_id = stack.outputs[1]['OutputValue']

    logger.info(region + ': Waiting for release build on ' +
                release_instance_id)
    logger.info(region + ': Waiting for profiling build on ' +
                release_instance_id)
    ec2 = session.client('ec2', region_name=region)
    waiter = ec2.get_waiter('instance_stopped')
    waiter.wait(
            InstanceIds=[release_instance_id, profiling_instance_id],
            WaiterConfig={
                'Delay': 30,
                'MaxAttempts': 120
            })

    stack.delete()
    waiter = cfn.meta.client.get_waiter('stack_delete_complete')
    waiter.wait(StackName=stack_name)

    s3 = session.client('s3', region_name='us-east-1')
    try:
        s3.head_object(Bucket=bucket_name, Key=perf_test_id + '/release/cbmc')
        s3.head_object(Bucket=bucket_name, Key=perf_test_id + '/release/goto-cc')
    except :
        logger.error(region + ': Release build failed')
        raise
    try:
        s3.head_object(Bucket=bucket_name, Key=perf_test_id + '/profiling/cbmc')
        s3.head_object(Bucket=bucket_name, Key=perf_test_id + '/profiling/goto-cc')
    except :
        logger.error(region + ': Profiling build failed')
        raise
    logger.info(region + ': builds completed and stack cleaned')


def prepare_sqs(session, region, perf_test_id, tasks):
    # create a bucket for storing artifacts
    logger = logging.getLogger('perf_test')

    cfn = session.resource('cloudformation', region_name=region)
    stack_name = 'perf-test-sqs-' + perf_test_id
    with open(same_dir('sqs.yaml')) as f:
        CFN_sqs = f.read()
    stack = cfn.create_stack(
            StackName=stack_name,
            TemplateBody=CFN_sqs,
            Parameters=[
                {
                    'ParameterKey': 'PerfTestId',
                    'ParameterValue': perf_test_id
                }
            ])

    waiter = cfn.meta.client.get_waiter('stack_create_complete')
    waiter.wait(StackName=stack_name, WaiterConfig={'Delay': 10})
    for o in stack.outputs:
        if o['OutputKey'] == 'QueueArn':
            arn = o['OutputValue']
        elif o['OutputKey'] == 'QueueName':
            queue = o['OutputValue']
        elif o['OutputKey'] == 'QueueUrl':
            url = o['OutputValue']
        else:
            assert(False)
    logger.info(region + ': SQS queues {}, {}-run set up'.format(
        queue, queue))

    seed_queue(session, region, queue, tasks)

    return (queue, arn, url)


def seed_queue(session, region, queue, task_set):
    # set up the tasks
    logger = logging.getLogger('perf_test')

    all_tasks = ['ConcurrencySafety-Main',
                 'MemSafety-Arrays',
                 'MemSafety-Heap', 'MemSafety-LinkedLists',
                 'MemSafety-MemCleanup',
                 'MemSafety-Other',
                 'NoOverflows-BitVectors', 'NoOverflows-Other',
                 'ReachSafety-Arrays', 'ReachSafety-BitVectors',
                 'ReachSafety-Combinations',
                 'ReachSafety-ControlFlow', 'ReachSafety-ECA',
                 'ReachSafety-Floats', 'ReachSafety-Heap',
                 'ReachSafety-Loops', 'ReachSafety-ProductLines',
                 'ReachSafety-Recursive', 'ReachSafety-Sequentialized',
                 'ReachSafety-XCSP',
                 'SoftwareSystems-AWS-C-Common-ReachSafety',
                 'SoftwareSystems-BusyBox-MemSafety',
                 'SoftwareSystems-BusyBox-NoOverflows',
                 'SoftwareSystems-DeviceDriversLinux64-ReachSafety',
                 'SoftwareSystems-DeviceDriversLinux64Large-ReachSafety',
                 'SoftwareSystems-OpenBSD-MemSafety',
                 'SoftwareSystems-uthash-MemSafety',
                 'SoftwareSystems-uthash-NoOverflows',
                 'SoftwareSystems-uthash-ReachSafety',
                 'Termination-MainControlFlow', 'Termination-MainHeap',
                 'Termination-Other']

    sqs = session.resource('sqs', region_name=region)
    queue = sqs.get_queue_by_name(QueueName=queue)
    if task_set == 'full':
        tasks = all_tasks
    elif task_set == 'quick':
        tasks = ['ReachSafety-Loops', 'ReachSafety-BitVectors']
    else:
        tasks = [t for t in all_tasks if re.match('^' + task_set + '$', t)]
        assert(tasks)

    for t in tasks:
        response = queue.send_messages(
                Entries=[
                    {'Id': '1', 'MessageBody': 'release-' + t},
                    {'Id': '2', 'MessageBody': 'profiling-' + t}
                ])
        assert(not response.get('Failed'))

    logger.info(region + ': SQS queue seeded with {} jobs'.format(
        len(tasks) * 2))


def run_perf_test(
        session, mode, region, vpc, subnets, ami, instance_type,
        sqs_arn, sqs_url,
        parallel, snapshot_id, instance_terminated_arn, bucket_name,
        perf_test_id, price, ssh_key_name, witness_check, compare_to, use_perf):
    # create an EC2 instance and trigger benchmarking
    logger = logging.getLogger('perf_test')

    if mode == 'spot':
        price = str(price*3)
    elif mode == 'on-demand':
        price = ''
    else:
        # Batch not yet implemented
        assert(False)

    stack_name = 'perf-test-exec-' + perf_test_id
    logger.info(region + ': Creating stack ' + stack_name)
    cfn = session.resource('cloudformation', region_name=region)
    with open(same_dir('ec2.yaml')) as f:
        CFN_ec2 = f.read()
    stack = cfn.create_stack(
            StackName=stack_name,
            TemplateBody=CFN_ec2,
            Parameters=[
                {
                    'ParameterKey': 'Ami',
                    'ParameterValue': ami
                },
                {
                    'ParameterKey': 'DefaultVPC',
                    'ParameterValue': vpc
                },
                {
                    'ParameterKey': 'Subnet',
                    'ParameterValue': subnets
                },
                {
                    'ParameterKey': 'InstanceType',
                    'ParameterValue': instance_type
                },
                {
                    'ParameterKey': 'SnapshotId',
                    'ParameterValue': snapshot_id
                },
                {
                    'ParameterKey': 'S3Bucket',
                    'ParameterValue': bucket_name
                },
                {
                    'ParameterKey': 'PerfTestId',
                    'ParameterValue': perf_test_id
                },
                {
                    'ParameterKey': 'SnsTopic',
                    'ParameterValue': instance_terminated_arn
                },
                {
                    'ParameterKey': 'SqsArn',
                    'ParameterValue': sqs_arn
                },
                {
                    'ParameterKey': 'SqsUrl',
                    'ParameterValue': sqs_url
                },
                {
                    'ParameterKey': 'MaxPrice',
                    'ParameterValue': price
                },
                {
                    'ParameterKey': 'FleetSize',
                    'ParameterValue': str(parallel)
                },
                {
                    'ParameterKey': 'SSHKeyName',
                    'ParameterValue': ssh_key_name
                },
                {
                    'ParameterKey': 'WitnessCheck',
                    'ParameterValue': str(witness_check)
                },
                {
                    'ParameterKey': 'CompareTo',
                    'ParameterValue': ':'.join(compare_to)
                },
                {
                    'ParameterKey': 'UsePerf',
                    'ParameterValue': str(use_perf)
                },
            ],
            Capabilities=['CAPABILITY_NAMED_IAM'])

    logger.info(region + ': Waiting for completition of ' + stack_name)
    waiter = cfn.meta.client.get_waiter('stack_create_complete')
    waiter.wait(StackName=stack_name)
    asg_name = stack.outputs[0]['OutputValue']
    asg = session.client('autoscaling', region_name=region)
    # make sure hosts that have been shut down don't come back
    asg.suspend_processes(
            AutoScalingGroupName=asg_name,
            ScalingProcesses=['ReplaceUnhealthy'])
    while True:
        res = asg.describe_auto_scaling_instances()
        if len(res['AutoScalingInstances']) == parallel:
            break
        logger.info(region + ': Waiting for AutoScalingGroup to be populated')
        time.sleep(10)
    # https://gist.github.com/alertedsnake/4b85ea44481f518cf157
    instances = [a['InstanceId'] for a in res['AutoScalingInstances']
                    if a['AutoScalingGroupName'] == asg_name]

    ec2 = session.client('ec2', region_name=region)
    for instance_id in instances:
        i_res = ec2.describe_instances(InstanceIds=[instance_id])
        name = i_res['Reservations'][0]['Instances'][0]['PublicDnsName']
        logger.info(region + ': Running benchmarks on ' + name)


def main():
    logging_format = "%(asctime)-15s: %(message)s"
    logging.basicConfig(format=logging_format)
    logger = logging.getLogger('perf_test')
    logger.setLevel('DEBUG')

    args = parse_args()

    # pick the most suitable region
    session = boto3.session.Session()
    (region, az, price, ami) = select_region(
            session, args.mode, args.region, args.instance_type)

    # fail early if key configuration would fail
    if args.ssh_key_name:
        ec2 = session.client('ec2', region_name=region)
        res = ec2.describe_key_pairs(
                Filters=[
                    {'Name': 'key-name', 'Values': [args.ssh_key_name]}
                ])
        if not args.ssh_key:
            assert(len(res['KeyPairs']) == 1)
        elif len(res['KeyPairs']):
            logger.warning(region + ': Key pair "' + args.ssh_key_name +
                           '" already exists, ignoring key material')
        else:
            with open(args.ssh_key) as kf:
                pk = kf.read()
                ec2.import_key_pair(
                        KeyName=args.ssh_key_name, PublicKeyMaterial=pk)

    # build a unique id for this performance test run
    perf_test_id = str(datetime.datetime.utcnow().strftime(
        '%Y-%m-%d-%H:%M:%S')) + '-' + args.commit_id
    perf_test_id = re.sub('[:/_\.\^~ ]', '-', perf_test_id)
    logger.info('global: Preparing performance test ' + perf_test_id)

    # target storage name
    account_id = session.client('sts').get_caller_identity()['Account']
    bucket_name = "perf-test-" + account_id
    # configuration set, let's create the infrastructure
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as e:
        session1 = boto3.session.Session()
        vpc_future = e.submit(
                get_default_vpc, session1, region, az)
        session2 = boto3.session.Session()
        sns_s3_future = e.submit(
                prepare_sns_s3, session2, args.email, bucket_name)

    (vpc, subnets, subnet_for_az) = vpc_future.result()
    instance_terminated_arn = sns_s3_future.result()

    with concurrent.futures.ThreadPoolExecutor(max_workers=3) as e:
        session1 = boto3.session.Session()
        build_future = e.submit(
                build, session1, region, ami, subnet_for_az,
                args.repository, args.commit_id, bucket_name, perf_test_id,
                args.build, args.use_perf)
        session2 = boto3.session.Session()
        ebs_future = e.submit(
                prepare_ebs, session2, region, az, ami,
                args.ssh_key_name)
        session3 = boto3.session.Session()
        sqs_future = e.submit(
                prepare_sqs, session3, region, perf_test_id, args.tasks)

    # wait for all preparation steps to complete
    build_future.result()
    snapshot_id = ebs_future.result()
    (queue, sqs_arn, sqs_url) = sqs_future.result()

    run_perf_test(
            session, args.mode, region, vpc, subnets, ami,
            args.instance_type,
            sqs_arn, sqs_url, args.parallel, snapshot_id,
            instance_terminated_arn, bucket_name, perf_test_id, price,
            args.ssh_key_name, args.witness_check, args.compare_to,
            args.use_perf)

    return 0


if __name__ == '__main__':
    rc = main()
    sys.exit(rc)
