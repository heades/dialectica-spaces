Dialectica Spaces
-----------------

This is a formalization of dialectica spaces in the two flavors from
Valeria de Paiva's thesis.  The first flavor is DC over Sets and the
second is GC over sets.  We call the latter Dial over sets.

Each type of space requires the notion of a lineale. A lineale is
essentially a symmetric monoidal closed category in the category of
partially ordered sets. (or A lineale corresponds to the
poset-reflection of the notion of a monoidal closed category).

- Basic definitions are defined in [ prelude.agda ]( prelude.agda )
- Lineales are defined in [lineale.agda](lineale.agda)
- Theorems about lineales can be found in [lineale-thms.agda](lineale-thms.agda)
- Definitions of concrete lineales can be found in [concrete-lineales.agda](concrete-lineales.agda)
- Colineales are defined in [colineale.agda](colineale.agda)
- Theorems about colineales can be found in [colineale-thms.agda](colineale-thms.agda)
- Definitions of concrete colineales can be found in [concrete-colineales.agda](concrete-colineales.agda)

Finally, we have the three types of dialectica spaces:

- DC over sets can be found in [DCSets.agda](DCSets.agda)
- Dial over sets can be found in [DialSets.agda](DialSets.agda)
- Non-commutative dial over sets can be found in [NCDialSets.agda](NCDialSets.agda)

Concurrency operators defined in DialSets instantiated to the three
element concrete lineale can be found in
[concurrency.agda](concurrency.agda).

This formalization was developed and tested with Agda 2.5.2 and
depends on the [Augusta University Agda Library](https://github.com/heades/AUGL). 
