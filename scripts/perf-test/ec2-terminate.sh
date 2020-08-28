#!/bin/bash
### BEGIN INIT INFO
# Provides: ec2-terminate
# Required-Start: $network $syslog
# Required-Stop:
# Default-Start:
# Default-Stop: 0 1 6
# Short-Description: ec2-terminate
# Description: send termination email
### END INIT INFO
#

case "$1" in
    start|status)
        exit 0
        ;;
    stop)
        # run the below
        ;;
    *)
        exit 1
        ;;
esac

# send instance-terminated message
# http://rogueleaderr.com/post/48795010760/how-to-notifyemail-yourself-when-an-ec2-instance/amp
ut=$(cat /proc/uptime | cut -f1 -d" ")
aws --region us-east-1 sns publish \
        --topic-arn #SNSTOPIC# \
        --message "instance terminating after $ut s at #MAXPRICE# USD/h"
sleep 3 # make sure the message has time to send
aws s3 cp /var/log/cloud-init-output.log \
  s3://#S3BUCKET#/#PERFTESTID#/$HOSTNAME.cloud-init-output.log

exit 0
