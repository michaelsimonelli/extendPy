#!/bin/bash

pip install git+https://github.com/dadadel/pyment.git

export QHOME=$PREFIX/q

mkdir -p $QHOME
mv extend.q reflect.p $QHOME
