#!/bin/bash
export QHOME=$PREFIX/q
QLIBDIR=l64

mkdir -p $QHOME
mkdir -p $QHOME/$QLIBDIR
mv extend.q reflect.p $QHOME
