#!/bin/bash

for dir in $*
do
	if [ -d "$dir" ];then
		rm -rf "$dir"
	fi
	mkdir $dir
done
rm trace*
