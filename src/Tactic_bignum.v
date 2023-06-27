Require Import Specific_bigint.
Require Import Specific_ops.
Require Import Float_full.

Module Float := SpecificFloat BigIntRadix2.
Module Interval := FloatIntervalFull Float.
