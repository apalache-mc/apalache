#!/usr/bin/env bash
#
# Produce diffs between the specifications.

for i in `seq 0 9`; do
    diff BinSearch${i}.tla BinSearch$((i+1)).tla >BinSearch$((i+1)).tla.patch
done

for i in `seq 2 9`; do
    diff MC${i}_8.tla MC$((i+1))_8.tla >MC$((i+1))_8.tla.patch
done
