/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.SourceCoverage

/-! Trust-boundary regression for the complete source-to-decoder composition. -/

open ReedSolomon.ListDecoding.FirstOrderCurveCandidates

#print axioms SourceCoverage.agreement_zero_of_source
#print axioms SourceCoverage.detected_of_source
#print axioms SourceCoverage.source_denominatorRegular
#print axioms SourceCoverage.decode_exact_of_source_coverage
