#!/bin/bash
set -x -e

# set up the additional volume
if lsblk | grep ^nvme
then
  d=$(ls /dev/nvme* | tail -n 1)
  e2fsck -f -y $d
  resize2fs $d
  mount $d /mnt
else
  e2fsck -f -y /dev/xvdf
  resize2fs /dev/xvdf
  mount /dev/xvdf /mnt
fi

# install packages
apt-get install -y git time wget binutils make jq
apt-get install -y zip unzip
apt-get install -y gcc libc6-dev-i386
apt-get install -y ant default-jdk python3-tempita python
if [ x:USE_PERF: = xTrue ]
then
  apt-get install -y linux-tools-*-aws
  git clone https://github.com/brendangregg/FlameGraph.git /mnt/FlameGraph
fi

# update benchmarks
cd /mnt/sv-benchmarks
git config remote.origin.fetch "+refs/heads/*:refs/remotes/origin/*"
git fetch origin master
git checkout -b master origin/master

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
  'https://gitlab.com/sosy-lab/sv-comp/bench-defs/-/raw/master/benchmark-defs/cbmc.xml?inline=false'
sed -i 's/witness.graphml/${logfile_path_abs}${taskdef_name}-witness.graphml/' cbmc.xml
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
      "https://gitlab.com/sosy-lab/sv-comp/bench-defs/-/raw/master/benchmark-defs/$def.xml?inline=false"
    sed -i 's#[\./]*/results-verified/LOGDIR/\${rundefinition_name}.\${taskdef_name}/witness.graphml#witnesses/${rundefinition_name}.${taskdef_name}-witness.graphml#' $def.xml
  done

  ln -s ../cpachecker/scripts/cpa.sh cpa.sh
  ln -s ../cpachecker/config/ config

  cd ../fshell-w2t
  git pull
  wget https://codeload.github.com/eliben/pycparser/zip/master -O pycparser-master.zip
  unzip pycparser-master.zip
  wget https://codeload.github.com/inducer/pycparserext/zip/master -O pycparserext-master.zip
  unzip pycparserext-master.zip
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
      poweroff
    fi

    # the queue is gone, or other host will be turning
    # off the lights
    poweroff
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
      --task $t -T 900s -M 15GB -o logs-$t/ -N $max_par -c -1
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
  elif [ x:USE_PERF: = xTrue ]
  then
    rm -f perf.data
    perf record --call-graph fp -o perf.data -- ../benchexec/bin/benchexec cbmc.xml --no-container \
      --task $t -T 600s -M 7GB -o logs-$t/ -N $max_par -c -1
    if timeout 2h perf report > sum.perf-graph-$t
    then
      gzip sum.perf-graph-$t
      aws s3 cp sum.perf-graph-$t.gz s3://:S3BUCKET:/:PERFTESTID:/$cfg/sum.perf-graph-$t.gz
    fi
    if timeout 2h perf report -g none --no-children > sum.perf-flat-$t
    then
      gzip sum.perf-flat-$t
      aws s3 cp sum.perf-flat-$t.gz s3://:S3BUCKET:/:PERFTESTID:/$cfg/sum.perf-flat-$t.gz
    fi
    if timeout 2h perf report -g graph,callee,count --no-children > sum.perf-callee-$t
    then
      gzip sum.perf-callee-$t
      aws s3 cp sum.perf-callee-$t.gz s3://:S3BUCKET:/:PERFTESTID:/$cfg/sum.perf-callee-$t.gz
    fi
    if timeout 2h perf script > sum.perf-folded-$t
    then
      ../FlameGraph/stackcollapse-perf.pl sum.perf-folded-$t > sum.perf-collapsed-$t
      ../FlameGraph/flamegraph.pl sum.perf-collapsed-$t > sum.perf-flamegraph-$t.svg
      aws s3 cp sum.perf-flamegraph-$t.svg s3://:S3BUCKET:/:PERFTESTID:/$cfg/sum.perf-flamegraph-$t.svg
    fi
    rm -f perf.data sum.perf-*-$t{,.gz}
  else
    rm -f gmon.sum gmon.out
    find . -name "*.gmon.out.*" -delete
    ../benchexec/bin/benchexec cbmc.xml --no-container \
      --task $t -T 600s -M 7GB -o logs-$t/ -N $max_par -c -1
    if ls *.gmon.out.* >/dev/null 2>&1
    then
      if timeout 2h gprof --sum ./cbmc-binary cbmc*.gmon.out.*
      then
        gprof ./cbmc-binary gmon.sum > sum.profile-$t
        aws s3 cp sum.profile-$t s3://:S3BUCKET:/:PERFTESTID:/$cfg/sum.profile-$t
      elif timeout 2h gprof ./cbmc-binary $(ls -S cbmc*.gmon.out.* | head -n 1) > single.profile-$t
      then
        aws s3 cp single.profile-$t s3://:S3BUCKET:/:PERFTESTID:/$cfg/single.profile-$t
      fi
      rm -f gmon.sum
      if timeout 2h gprof --sum ./goto-cc goto-cc*.gmon.out.*
      then
        gprof ./goto-cc gmon.sum > sum.goto-cc-profile-$t
        aws s3 cp sum.goto-cc-profile-$t \
          s3://:S3BUCKET:/:PERFTESTID:/$cfg/sum.goto-cc-profile-$t
      elif timeout 2h gprof ./goto-cc $(ls -S goto-cc*.gmon.out.* | head -n 1) > single.goto-cc-profile-$t
      then
        aws s3 cp single.goto-cc-profile-$t \
          s3://:S3BUCKET:/:PERFTESTID:/$cfg/single.goto-cc-profile-$t
      fi
      rm -f gmon.sum gmon.out
      find . -name "cbmc*.gmon.out.*" -delete
      find . -name "goto-cc*.gmon.out.*" -delete
    fi
    rm -f sum.profile-$t sum.goto-cc-profile-$t
    rm -f single.profile-$t single.goto-cc-profile-$t
  fi
  rm -rf logs-$t
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
