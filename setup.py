#!/usr/bin/env python

from setuptools import setup, find_packages

import pathlib

here = pathlib.Path(__file__).parent.resolve()

setup(name='oo_scoping',
      version='1.0',
      description='Object-Oriented state abstraction',
      long_description=(here / 'README.md').read_text(encoding='utf-8'),
      author='Redacted',
      author_email='Redacted',
      url='Redacted',
      install_requires=[
          'z3-solver'
      ]
)