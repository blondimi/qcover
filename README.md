# QCover

QCover is a Python implementation of a decision procedure for the Petri net coverability problem that is based on applying reachability in continuous Petri nets as a pruning criterion inside a backward-coverability framework. The heart of the approach is a sophisticated encoding of reachability in continuous Petri nets into SMT which then enables QCover to use the SMT solver Z3 in order to decide such reachability problems. QCover can also be used to decide reachability and coverability in continuous Petri nets.

## Installation

QCover does not require any installation. However, [Python 2.7](https://www.python.org/download/releases/2.7/) must be installed with the following additional packages:

* [NumPy](http://www.numpy.org/) ≥1.8.2 (e.g. on Debian-based Linux distributions: `sudo apt-get install python-numpy`),
* [SciPy](https://www.scipy.org/) ≥0.13.3 (e.g. on Debian-based Linux distributions: `sudo apt-get install python-scipy`),
* [Z3](https://github.com/Z3Prover/) ≥4.4.0: follow installation instructions for Python bindings.

## Usage

QCover can be executed by simply entering `python main.py file_to_verify`. For example, the Petri net given [here](https://github.com/blondimi/qcover/tree/master/examples/lamport) for Lamport's mutual exclusion algorithm can be proven safe as follows:

```
> python main.py ../examples/lamport/model.spec
Safe
```

QCover has an experimental parallel mode that can be activated by switching `parallel` to `True` in `config.py`.

## Input file format

QCover supports *strict subsets of* two input file formats:

* `.spec` format from [mist](https://github.com/pierreganty/mist) described [here](https://github.com/pierreganty/mist/wiki#input-format-of-mist),
* `.tts` format from [Bfc](http://www.cprover.org/bfc/) described [here](http://www.cprover.org/bfc/#TTS).

QCover loads `.spec` files as Petri nets and executes the backward coverability algorithm based on continuous reachability pruning described in \[[BFHH16](#references), [BFHH17](#references)\] (see references below). Currently, QCover loads `.tts` files as vector addition systems with states (VASS) and executes a backward coverability algorithm with ℤ-VASS reachability pruning.  This feature is experimental and is not described in \[[BFHH16](#references), [BFHH17](#references)\].

Both input file formats can be translated to the other format using, e.g., [`ttstrans`](https://github.com/pevalme/bfc_fork) and [`spec2tts`](http://www.cprover.org/bfc/#DOWNLOAD).

## Benchmarking and TACAS'16 release

The current version of QCover differs slightly from the version that was tested in \[[BFHH16](#references)\]. Its code has been improved for adaptability and extendability. Benchmarking can be done using the original TACAS'16 version found in [`./tacas16/`](https://github.com/blondimi/qcover/tree/master/tacas16).

## Questions

For any question concerning QCover, contact [Michael Blondin](https://www7.in.tum.de/~blondin/#contact) or [Christoph Haase](http://www.lsv.ens-cachan.fr/~haase/index.html#info).

## References

**[BFHH16]** [Michael Blondin, Alain Finkel, Christoph Haase and Serge Haddad. *Approaching the Coverability Problem Continuously*. Proc. 22<sup>nd</sup> International Conference Tools and Algorithms for the Construction and Analysis of Systems (TACAS), Springer, 2016](http://dx.doi.org/10.1007/978-3-662-49674-9_28). Available online [here](https://www7.in.tum.de/~blondin/papers/BFHH16.pdf).

**[BFHH17]** Michael Blondin, Alain Finkel, Christoph Haase and Serge Haddad. *The Logical View on Continuous Petri Nets*. Invited submission to the special issue of selected TACAS'16 papers, ACM Transactions on Computational Logic (TOCL), 2017. Available online [here](https://www7.in.tum.de/~blondin/papers/BFHH17.pdf).
