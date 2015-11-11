#!/bin/bash

src=$1
dst=$2

if [ -z "$src" ]; then
	echo "缺少源文件位置\n"
elif [ -z "$dst" ]; then
	echo "缺少目标文件夹位置\n"
elif [ "${src:0:1}" != "/" ]; then
	echo "传入的源文件路径不是绝对路径\n"
elif [ "${dst:0:1}" != "/" ]; then
	echo "传入的目标文件夹路径不是绝对路径\n"
else
	mv $src $dst
fi


