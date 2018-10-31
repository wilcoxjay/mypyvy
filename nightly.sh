#!/usr/bin/env bash

TAG=nightly
ARGS=

while [ $# -ne 0 ]; do
    case "$1" in
        --args)
            ARGS="$@"  # include --args
            while [ $# -ne 0 ]; do
                shift
            done
            break
            ;;
        --tag)
            shift
            if [ $# -eq 0 ]; then
                echo "--tag expects an argument"
                exit 1
            fi
            TAG="$1"
            ;;
        *)
            echo "unrecognized argument $1"
            exit 1
            ;;
    esac
    shift

done


LOGDIR=logs/$(date '+%y%m%d-%H%M%S')-$TAG
time python3 benchmark.py -n 1000 -j 4 --timeout 75 --pin-cores --keep-logs $LOGDIR $ARGS

pushd $LOGDIR
tar cfz logs.tgz *.log
rm *.log
popd

git add $LOGDIR
