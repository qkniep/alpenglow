---- MODULE MC_Liveness ----
(*
  Model Checking instance for LivenessAlpenglow
  
  This module wraps LivenessAlpenglow.tla for TLC model checking.
  The Spec, constants, and properties are defined in MC_Liveness.cfg
*)

EXTENDS LivenessAlpenglow

\* All definitions inherited from LivenessAlpenglow:
\* - Spec (with fairness constraints for liveness)
\* - Init, Next, vars
\* - All liveness properties (temporal logic)

=============================================================================
