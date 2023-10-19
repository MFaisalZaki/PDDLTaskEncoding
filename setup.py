#!/usr/bin/env python3

from setuptools import setup, find_packages  # type: ignore
from PDDLTaskEncoding import PDDLTaskEncoding


setup(
    name="PDDLTaskEncoding",
    version=PDDLTaskEncoding.__version__,
    description="PDDL to SMT Encoding Framework",
    long_description="TODO",
    long_description_content_type="text/markdown",
    author="TODO:",
    author_email="TODO",
    url="TODO",
    packages=find_packages()
    include_package_data=True,
    python_requires=">=3.8",
    install_requires=["z3-solver", "unified-planning"],
    extras_require={},
    license="APACHE",
    keywords="planning logic SMT PDDL",
    classifiers=[
        "Development Status :: 3 - Alpha",
        "Intended Audience :: Science/Research",
        "Intended Audience :: Developers",
        "Topic :: Scientific/Engineering :: Artificial Intelligence",
        "License :: OSI Approved :: Apache Software License",
        "Programming Language :: Python :: 3.8",
        "Programming Language :: Python :: 3.9",
        "Programming Language :: Python :: 3.10",
        "Programming Language :: Python :: 3.11",
    ],
    entry_points={}
)