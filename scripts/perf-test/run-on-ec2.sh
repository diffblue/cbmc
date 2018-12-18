#!/bin/bash
set -x -e

# set up the additional volume
sleep 10
e2fsck -f -y /dev/xvdf
resize2fs /dev/xvdf
mount /dev/xvdf /mnt

# install packages
apt-get install -y git time wget binutils make jq
apt-get install -y zip unzip
apt-get install -y gcc libc6-dev-i386
apt-get install -y ant python3-tempita python

# cgroup set up for benchexec
chmod o+wt '/sys/fs/cgroup/cpuset/'
chmod o+wt '/sys/fs/cgroup/cpu,cpuacct/user.slice'
chmod o+wt '/sys/fs/cgroup/memory/user.slice'
chmod o+wt '/sys/fs/cgroup/freezer/'

# update benchmarks
cd /mnt/sv-benchmarks
git pull

# update benchexec
cd /mnt/benchexec
git pull

# prepare for tool packaging
cd /mnt
cd cprover-sv-comp
git pull
mkdir -p src/cbmc src/goto-cc
touch LICENSE
cd ..
mkdir -p run
cd run
wget -O cbmc.xml \
  https://raw.githubusercontent.com/sosy-lab/sv-comp/master/benchmark-defs/cbmc.xml
sed -i 's/witness.graphml/${logfile_path_abs}${inputfile_name}-witness.graphml/' cbmc.xml
cd ..
mkdir -p tmp
export TMPDIR=/mnt/tmp

if [ x:WITNESSCHECK: = xTrue ]
then
  cd cpachecker
  git pull
  ant

  cd ../run
  for def in \
    cpa-seq-validate-correctness-witnesses \
    cpa-seq-validate-violation-witnesses \
    fshell-witness2test-validate-violation-witnesses
  do
    wget -O $def.xml \
      https://raw.githubusercontent.com/sosy-lab/sv-comp/master/benchmark-defs/$def.xml
    sed -i 's#[\./]*/results-verified/LOGDIR/\${rundefinition_name}.\${inputfile_name}.files/witness.graphml#witnesses/${rundefinition_name}.${inputfile_name}-witness.graphml#' $def.xml
  done

  ln -s ../cpachecker/scripts/cpa.sh cpa.sh
  ln -s ../cpachecker/config/ config

  cd ../fshell-w2t
  git pull
  wget https://codeload.github.com/eliben/pycparser/zip/master -O pycparser-master.zip
  unzip pycparser-master.zip
  cd ../run
  cp -a ../fshell-w2t/* .
fi

# reduce the likelihood of multiple hosts processing the
# same message (in addition to SQS's message hiding)
sleep $(expr $RANDOM % 30)
retry=1

while true
do
  sqs=$(aws --region :AWSREGION: sqs receive-message --queue-url :SQSURL: | \
    jq -r '.Messages[0].Body,.Messages[0].ReceiptHandle')

  if [ -z "$sqs" ]
  then
    # no un-read messages in the input queue; let's look
    # at -run
    n_msgs=$(aws --region :AWSREGION: sqs get-queue-attributes \
      --queue-url :SQSURL:-run --attribute-names ApproximateNumberOfMessages | \
      jq -r '.Attributes.ApproximateNumberOfMessages')

    if [ $retry -eq 1 ]
    then
      retry=0
      sleep 30
      continue
    elif [ -n "$n_msgs" ] && [ "$n_msgs" = "0" ]
    then
      # shut down the infrastructure
      aws --region us-east-1 sns publish --topic-arn :SNSTOPIC: \
        --message "Trying to delete stacks in :AWSREGION:"
      aws --region :AWSREGION: cloudformation delete-stack --stack-name \
        perf-test-sqs-:PERFTESTID:
      aws --region :AWSREGION: cloudformation delete-stack --stack-name \
        perf-test-exec-:PERFTESTID:
      halt
    fi

    # the queue is gone, or other host will be turning
    # off the lights
    halt
  fi

  retry=1
  bm=$(echo $sqs | cut -f1 -d" ")
  cfg=$(echo $bm | cut -f1 -d"-")
  t=$(echo $bm | cut -f2- -d"-")
  msg=$(echo $sqs | cut -f2- -d" ")

  # mark $bm in-progress
  aws --region :AWSREGION: sqs send-message --queue-url :SQSURL:-run \
    --message-body $bm-$(hostname)

  # there is no guarantee of cross-queue action ordering
  # sleep for a bit to reduce the likelihood of missing
  # in-progress messages while the input queue is empty
  sleep 3

  # remove it from the input queue
  aws --region :AWSREGION: sqs delete-message \
    --queue-url :SQSURL: --receipt-handle $msg

  cd /mnt/cprover-sv-comp
  rm -f src/cbmc/cbmc src/goto-cc/goto-cc
  aws s3 cp s3://:S3BUCKET:/:PERFTESTID:/$cfg/cbmc src/cbmc/cbmc
  aws s3 cp s3://:S3BUCKET:/:PERFTESTID:/$cfg/goto-cc src/goto-cc/goto-cc
  chmod a+x src/cbmc/cbmc src/goto-cc/goto-cc
  make CBMC=. cbmc.zip
  cd ../run
  rm -f cbmc cbmc-binary goto-cc
  unzip ../cprover-sv-comp/cbmc.zip
  mv cbmc cbmc-zip
  mv cbmc-zip/* .
  rmdir cbmc-zip
  rm ../cprover-sv-comp/cbmc.zip

  date
  echo "Task: $t"

  # compute the number of possible executors
  max_par=$(cat /proc/cpuinfo | grep ^processor | wc -l)
  mem=$(free -g | grep ^Mem | awk '{print $2}')
  if [ $cfg != "profiling" ]
  then
    mem=$(expr $mem / 15)
  else
    mem=$(expr $mem / 7)
  fi
  if [ $mem -lt $max_par ]
  then
    max_par=$mem
  fi

  if [ $cfg != "profiling" ]
  then
    ../benchexec/bin/benchexec cbmc.xml --no-container \
      --task $t -T 900s -M 15GB -o logs-$t/ -N $max_par -c 1
    if [ -d logs-$t/cbmc.*.logfiles ]
    then
      cd logs-$t
      tar czf witnesses.tar.gz cbmc.*.logfiles
      rm -rf cbmc.*.logfiles
      cd ..

      if [ x:WITNESSCHECK: = xTrue ]
      then
        for wc in *-witnesses.xml
        do
          wcp=$(echo $wc | sed 's/-witnesses.xml$//')
          mkdir witnesses
          tar -C witnesses --strip-components=1 -xzf logs-$t/witnesses.tar.gz
          ../benchexec/bin/benchexec --no-container \
            $wc --task $t -T 90s -M 15GB -o $wcp-logs-$t/ -N $max_par -c 1
          rm -rf witnesses
        done
      fi
    fi
    start_date="$(echo :PERFTESTID: | cut -f1-3 -d-)"
    start_date="$start_date $(echo :PERFTESTID: | cut -f4-6 -d- | sed 's/-/:/g')"
    for l in *logs-$t/*.xml.bz2
    do
      cd $(dirname $l)
      bunzip2 *.xml.bz2
      perl -p -i -e \
        "s/^(<result.*version=\"[^\"]*)/\$1::PERFTESTID:/" *.xml
      perl -p -i -e \
        's/systeminfo hostname=".*"/systeminfo hostname=":INSTANCETYPE:"/' *.xml
      perl -p -i -e \
        "s/^(<result.*date=)\"[^\"]*/\$1\"$start_date/" *.xml
      bzip2 *.xml
      cd ..
    done

    compare_to=""
    if [ x:WITNESSCHECK: = xTrue ]
    then
      compare_to="*-logs-$t/*.xml.bz2"
    fi
    for c in $(echo :COMPARETO: | sed 's/:/ /g')
    do
      if aws s3 ls s3://:S3BUCKET:/$c/$cfg/logs-$t/
      then
        aws s3 sync s3://:S3BUCKET:/$c/$cfg/logs-$t logs-$t-$c
        compare_to="$compare_to logs-$t-$c/*.xml.bz2"
      fi
    done

    ../benchexec/bin/table-generator logs-$t/*xml.bz2 $compare_to -o logs-$t/
    aws s3 cp logs-$t s3://:S3BUCKET:/:PERFTESTID:/$cfg/logs-$t/ --recursive
    for wc in *-witnesses.xml
    do
      [ -s $wc ] || break
      wcp=$(echo $wc | sed 's/-witnesses.xml$//')
      [ -d $wcp-logs-$t ] || continue
      rm -rf $wcp-logs-$t/*.logfiles
      aws s3 cp $wcp-logs-$t s3://:S3BUCKET:/:PERFTESTID:/$cfg/$wcp-logs-$t/ --recursive
    done
  else
    rm -f gmon.sum gmon.out *.gmon.out.*
    ../benchexec/bin/benchexec cbmc.xml --no-container \
      --task $t -T 600s -M 7GB -o logs-$t/ -N $max_par -c 1
    if ls *.gmon.out.* >/dev/null 2>&1
    then
      gprof --sum ./cbmc-binary cbmc*.gmon.out.*
      gprof ./cbmc-binary gmon.sum > sum.profile-$t
      rm -f gmon.sum
      gprof --sum ./goto-cc goto-cc*.gmon.out.*
      gprof ./goto-cc gmon.sum > sum.goto-cc-profile-$t
      rm -f gmon.sum gmon.out
      rm -f cbmc*.gmon.out.*
      rm -f goto-cc*.gmon.out.*
      aws s3 cp sum.profile-$t s3://:S3BUCKET:/:PERFTESTID:/$cfg/sum.profile-$t
      aws s3 cp sum.goto-cc-profile-$t \
        s3://:S3BUCKET:/:PERFTESTID:/$cfg/sum.goto-cc-profile-$t
    fi
  fi
  rm -rf logs-$t sum.profile-$t
  date

  # clear out the in-progress message
  while true
  do
    sqs=$(aws --region :AWSREGION: sqs receive-message --queue-url :SQSURL:-run \
      --visibility-timeout 10 | jq -r '.Messages[0].Body,.Messages[0].ReceiptHandle')
    bm2=$(echo $sqs | cut -f1 -d" ")
    msg2=$(echo $sqs | cut -f2- -d" ")

    if [ "$bm2" = "$bm-$(hostname)" ]
    then
      aws --region :AWSREGION: sqs delete-message --queue-url :SQSURL:-run \
        --receipt-handle $msg2
      break
    fi
  done
done
