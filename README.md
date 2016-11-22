reducerabinpairs
================
[![Build Status](https://travis-ci.org/44534/reducerabinpairs.svg?branch=master)](https://travis-ci.org/44534/reducerabinpairs)

A module to reduce the acceptance condition of a deterministic Rabin automaton.

Features
--------
* Reductions independend of the transition system of the automaton
* Reductions depending on the transition system of the automaton

Programm
--------
The package contains the executable `reducerabinpairs` to apply the reductions to a deterministic Rabin automaton. The automaton has to be specified in Hanoi-Omega-Automata format.

The supported options are:
```
> reducerabinpairs -h
reducerabinpairs

Usage: reducerabinpairs [--top]
                        --do (split | combine | reduce | sat | irred | all)
  reduce the acceptance condition of a deterministic Rabin automaton

Available options:
  -h,--help                Show this help text
  --top                    use reduction depending on the transition system of
                           the automaton
  --do (split | combine | reduce | sat | irred | all)
                           apply one or all reductions

```



Install
-------
Dependency: omega-automata

```
stack install
```
