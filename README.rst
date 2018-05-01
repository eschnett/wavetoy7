`wavetoy7 <https://github.com/eschnett/wavetoy7>`__
===================================================

|Build Status| |Coverage Status|

A progression of WaveToy implementations in Haskell.

Problem description
-------------------

.. math::

   \partial_{tt} u = \partial_{xx} u

Build instructions
------------------

.. code:: sh

    # Build the project:
    stack build

    # Run the test suite:
    stack test

    # Run the benchmarks:
    stack bench

    # Generate documentation:
    stack haddock

.. |Build Status| image:: https://travis-ci.org/eschnett/wavetoy7.svg?branch=master
   :target: https://travis-ci.org/eschnett/wavetoy7
.. |Coverage Status| image:: https://coveralls.io/repos/github/eschnett/wavetoy7/badge.svg?branch=master
   :target: https://coveralls.io/github/eschnett/wavetoy7?branch=master
