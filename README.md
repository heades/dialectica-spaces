Dialectica Spaces
-----------------

This is a formalization of dialectica spaces on the category DC in
sets from Valeria de Paiva's thesis. 

Dialectica spaces require the notion of a lineale. A lineale is
essentially a symmetric monoidal closed category in the category of
partially ordered sets. (or a lineale corresponds to the
poset-reflection of the notion of a monoidal closed category).

- Lineales are defined in [lineale.agda](lineale.agda)
- Theorems about lineales can be found in [lineale-thms.agda](lineale-thms.agda)
- Definitions of concrete lineales can be found in [concrete-lineales.agda](concrete-lineales.agda)

Finally, we have dialectica spaces:

- DC in sets can be found in [DCSets.agda](DCSets.agda)

This formalization was developed and tested with Agda 2.4.2.4 and
depends on the [Augusta University Agda Library](https://github.com/heades/AUGL).