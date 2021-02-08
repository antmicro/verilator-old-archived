#!/bin/bash
cd Surelog && make PREFIX=$PWD/../image/ release install -j $(nproc) && cd ..
autoconf && ./configure --prefix=$PWD/image && make install
make -C vcddiff PREFIX=./image -j $(nproc)
cp -p vcddiff/vcddiff image/bin/vcddiff
