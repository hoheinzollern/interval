Version 4.11.0
--------------

* added commands `Def` and `Do` to ease the use of degenerate forms of tactics
* made the tactics recognize `F2R` from Flocq
* added tactic `assert_float` in `Language`
* minimal Coq version is now 8.13

Version 4.10.0
--------------

* ensured compatibility from Coq 8.11 to 8.19
* optimized `exp` for native floating-point numbers
* allowed goals with strict inequalities, e.g., `f1 < e <= f2`
* strengthened specifications of `FloatOps.{mul,div}_{DN,UP}`

Version 4.9.0
-------------

* added support for fixed-point rounding operators from Flocq
* made the tactics recognize the elementary error `round x - x`
* tightened enclosures of floating-point rounding operators and errors

Version 4.8.1
-------------

* ensured compatibilty from Coq 8.11 to 8.18

Version 4.8.0
-------------

* tightened enclosures of rounding operators and errors
* added an experimental framework for verification of floating-point expressions in `Language`

Version 4.7.0
-------------

* ensured compatibility from Coq 8.11 to 8.17
* made the tactics a bit more robust against unknown symbols
* changed the degenerate tactics so that they always use `i_delay`

Version 4.6.1
-------------

* ensured compatibility from Coq 8.8 to 8.17
* made `integral` a bit more lenient on `(ln t)^n` bounding integrands

Version 4.6.0
-------------

* added option `i_decimal` for producing decimal enclosures
* added support for floating-point rounding operators from Flocq

Version 4.5.2
-------------

* ensured compatibility from Coq 8.8 to 8.16

Version 4.5.1
-------------

* fixed behavior of `root` on unbounded intervals

Version 4.5.0
-------------

* added tactics `root` and `root_intro` for refining enclosures using Newton's method
* improved behavior of `exp` in case of overflow

Version 4.4.0
-------------

* ensured compatibility from Coq 8.8 to 8.15
* made `interval` and `integral` usable in tactic-in-term contexts

Version 4.3.1
-------------

* made plotting more reliable when an output bound is close to zero

Version 4.3.0
-------------

* ensured compatibility from Coq 8.8 to 8.14
* made reification unfold transparent constants
* added reification of `Q2R` and thus of rational literals

Version 4.2.0
-------------

* added tactic `plot` for computing a function graph
* added command `Plot` for passing a function graph to Gnuplot (requires Coq >= 8.11)

Version 4.1.1
-------------

* made reification of `IZR`, `pow`, `powerRZ`, and `bpow`, more robust

Version 4.1.0
-------------

* ensured compatibility from Coq 8.8 to 8.13
* added support for strict inequalities in hypotheses

Version 4.0.0
-------------

* ensured compatibility from Coq 8.8 to 8.12
* made native floating-point computations the default:
  - they are enabled when `i_prec` is not specified
  - this requires support from both Coq (e.g., 8.11) and Flocq (e.g., 3.3)
  - if support is missing, the tactic behaves as if passed `i_prec 53`
* improved handling of bisection:
  - `i_bisect` can now be passed several times, to split along several variables
  - automatic differentiation is now enabled by `i_autodiff` (was `i_bisect_diff`)
  - Taylor models are enabled by `i_taylor` (was `i_bisect_taylor`)
  - automatic differentiation and Taylor models no longer implies bisection,
    so `i_bisect` should also be passed if needed
* moved support of integrals from `interval` to a dedicated tactic `integral`:
  - only one integral can occur in the goal, but its enclosure is refined until the goal is proved
  - bisection is not supported
  - `i_fuel` controls the maximal number of sub-intervals (replaces `i_integral_depth`)
  - `i_degree` controls the size of the polynomials (was `i_integral_deg`)
* moved support of integrals from `interval_intro` to a dedicated tactic `integral_intro`:
  - the expression has to be an integral
  - `i_width` controls the width of the computed enclosure (was `i_integral_width`)
  - `i_relwidth` controls the accuracy of the computed enclosure (was `i_integral_prec`)

Version 3.4.2
-------------

* ensured compatibility from Coq 8.7 to 8.11

Version 3.4.1
-------------

* ensured compatibility from Coq 8.7 to 8.10

Version 3.4.0
-------------

* moved to Flocq 3.0; minimal Coq version is now 8.7
* added support for `Ztrunc`, `Zfloor`, etc
* added support for constants written using `bpow radix2`

Version 3.3.0
-------------

* added option `i_integral_width` for absolute width of integrals
* added option `i_native_compute` to use `native_compute` instead of `vm_compute`
* added option `i_delay` to avoid immediate check (mostly useful for `interval_intro`)
* improved accuracy for interval `cos` and `sin` away from zero
* ensured compatibility from Coq 8.5 to Coq 8.7

Version 3.2.0
-------------

* added support for some improper integrals using `RInt_gen`

Version 3.1.1
-------------

* ensured compatibility with Coq 8.6

Version 3.1.0
-------------

* improved tactic so that it can be used with backtracking tacticals (`try`, `||`)
* fixed ineffective computation of integrals with reversed or overlapping bounds

Version 3.0.0
-------------

* added support for integrals using Coquelicot's `RInt` operator
* improved support for Taylor models

Version 2.2.1
-------------

* moved to MathComp 1.6

Version 2.2.0
-------------

* improved tactic so that it handles goals with non floating-point bounds
* added a dependency on Coquelicot to remove an assumption about `ln`

Version 2.1.0
-------------

* moved to Flocq 2.5

Version 2.0.0
-------------

* added support for Taylor models (`i_bisect_taylor`)
* added support for `ln`
* improved tactic so that it handles hypotheses with non floating-point bounds

Version 1.1.0
-------------

* moved to Flocq 2.4
* added support for disequalities to the tactic
* added support for the `PI` symbol
* enlarged the domain of the interval versions of `cos` and `sin`

Version 1.0.0
-------------

* removed remaining axioms

Version 0.16.2
--------------

* fixed install rule on case-insensitive filesystems

Version 0.16.1
--------------

* removed the custom definition of `atan` and used the one from Coq 8.4

Version 0.16.0
--------------

* switched build system to `remake`
* moved to Coq 8.4

Version 0.15.1
--------------

* fixed failures when combining `interval_intro` with `i_bisect*`

Version 0.15.0
--------------

* added support for strict inequalities to the tactic
* added support for integer power to the tactic
* improved support for absolute value in the tactic
* improved tactic so that it directly handles `e1 <= e2`

Version 0.14.0
--------------

* sped up square root for `Z`-based floating-point numbers
* improved readability of the error messages for the tactic
* modularized the tactic so that other specializations are available to user code
* moved to Flocq 2.0

Version 0.13.0
--------------

* moved to Coq 8.3

Version 0.12.1
--------------

* fixed an incompatibility with Flocq 1.2

Version 0.12
------------

* added a dependency on the Flocq library

Version 0.11
------------

* removed `i_nocheck` parameter as computations are no longer done at `Qed` time
