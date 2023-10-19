#!/usr/bin/env python3

from setuptools import setup, find_packages  # type: ignore
import PDDLTaskEncoding


# setup.py
setup(
    name="PDDLTaskEncoding",
    version=PDDLTaskEncoding.__version__,
    description="A package for PDDL task encodings",
    author="Your Name",
    author_email="your@email.com",
    packages=find_packages(),
    install_requires=[ "z3-solver", "unified-planning" ],
    py_modules=["PDDLTaskEncoding"],
)
