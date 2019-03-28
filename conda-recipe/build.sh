#!/bin/bash
#conda install -c kx embedPy

pip install git+https://github.com/dadadel/pyment.git

export QHOME=$PREFIX/q
QLIBDIR=l64

mkdir -p $QHOME
mkdir -p $QHOME/$QLIBDIR
mv extend.q reflect.p $QHOME
