#!/bin/bash
set -ex
cd Surelog && make PREFIX=$PWD/../image/ release install -j $(nproc) && cd ..
autoconf && ./configure --prefix=$PWD/image SURELOG_INSTALL_DIR=$PWD/image && make -j $(nproc) && make install
make -C vcddiff PREFIX=./image -j $(nproc)
cp -p vcddiff/vcddiff image/bin/vcddiff
