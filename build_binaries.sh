#!/bin/bash
set -ex
export SURELOG_INSTALL_DIR=$PWD/image
cd Surelog && make PREFIX=$SURELOG_INSTALL_DIR release install -j $(nproc) && cd ..
autoconf && ./configure --prefix=$PWD/image && make -j $(nproc) && make install
make -C vcddiff PREFIX=./image -j $(nproc)
cp -p vcddiff/vcddiff image/bin/vcddiff
