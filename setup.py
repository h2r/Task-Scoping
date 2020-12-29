#!/usr/bin/env python

from setuptools import setup, find_packages

import pathlib

here = pathlib.Path(__file__).parent.resolve()

setup(name='oo_scoping',
      version='1.0',
      description='Object-Oriented state abstraction',
      long_description=(here / 'README.md').read_text(encoding='utf-8'),
      author='Michael Fishman and Nishanth Kumar',
      author_email='michaeljfishman@protonmail.com, nishanth_kumar@brown.edu',
      url='https://github.com/h2r/OO-Scoping-IPC',
      install_requires=[
          'z3-solver'
      ]
)