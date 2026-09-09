/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

-- Substrate
import LevyStochCalc.Basic
-- LevyStochCalc.Notation was a 21-line empty placeholder (no content, only
-- a copyright header + namespace declaration); deleted per red-team P1 F1
-- 2nd audit 2026-05-23. If notation needs to be reserved across the project
-- in the future, recreate the file with the specific notation declarations.

-- Layer 0: Compensated Poisson
import LevyStochCalc.Analysis.GronwallIntegral
import LevyStochCalc.Analysis.CadlagJumps
import LevyStochCalc.Analysis.GronwallIterate
import LevyStochCalc.Analysis.DyadicGrid
import LevyStochCalc.Analysis.FiniteJumpSum
import LevyStochCalc.Analysis.ScaledTrig
import LevyStochCalc.Analysis.SortedGrid
import LevyStochCalc.Probability.AbsMoment
import LevyStochCalc.Probability.IndepGrouping
import LevyStochCalc.Probability.IndepLimit
import LevyStochCalc.Probability.IndepJoin
import LevyStochCalc.Probability.ComapTuple
import LevyStochCalc.Probability.TrivialSigma
import LevyStochCalc.Probability.IntegerValuedMeasure
import LevyStochCalc.Probability.MarkedPredictable
import LevyStochCalc.Probability.Progressive
import LevyStochCalc.Probability.StoppedProgressive
import LevyStochCalc.Probability.ExitTime
import LevyStochCalc.Probability.ProgressiveCadlag
import LevyStochCalc.Probability.Predictable
import LevyStochCalc.Probability.PredictableModification
import LevyStochCalc.Probability.MarkedPredictableModification
import LevyStochCalc.Probability.CharTotal
import LevyStochCalc.Probability.SetIntegralPiSystem
import LevyStochCalc.Probability.CharCylinder
import LevyStochCalc.Probability.PairingFubini
import LevyStochCalc.Probability.IndepBlocks
import LevyStochCalc.Probability.GaussianSum
import LevyStochCalc.Probability.DoobContinuous
import LevyStochCalc.Probability.Transport
import LevyStochCalc.Probability.Augmentation
import LevyStochCalc.Probability.SubSigmaLimit
import LevyStochCalc.Probability.AugmentationMeasurable
import LevyStochCalc.Probability.ProjectionLimit
import LevyStochCalc.Probability.AEMeasurableInf
import LevyStochCalc.Probability.CondExpInf
import LevyStochCalc.Probability.CondExpRightContinuous
import LevyStochCalc.Probability.Quasimartingale
import LevyStochCalc.Probability.FiltrationNNReal
import LevyStochCalc.Probability.CondExpModification
import LevyStochCalc.Poisson.RegionPartition
import LevyStochCalc.Poisson.ZeroIntensity
import LevyStochCalc.Poisson.PoissonSplitting
import LevyStochCalc.Poisson.PoissonSuperposition
import LevyStochCalc.Poisson.RegionIndependence
import LevyStochCalc.Poisson.RandomMeasure
import LevyStochCalc.Poisson.Restrict
import LevyStochCalc.Poisson.FiniteActivity
import LevyStochCalc.Poisson.Atomic
import LevyStochCalc.Poisson.Compensator
import LevyStochCalc.Poisson.CompensatorL1
import LevyStochCalc.Poisson.JumpSum
import LevyStochCalc.Poisson.SimplePathwise
import LevyStochCalc.Poisson.MarkStepPathwise
import LevyStochCalc.Poisson.PathwiseIdentity
import LevyStochCalc.Poisson.Simplicity
import LevyStochCalc.Poisson.ChainRule
import LevyStochCalc.Poisson.StrictCount
import LevyStochCalc.Poisson.SimpleCharacter
import LevyStochCalc.Poisson.CharacterIntegrand
import LevyStochCalc.Poisson.WindowFiltration
import LevyStochCalc.Poisson.CharacterOrthogonal
import LevyStochCalc.Poisson.CharacterTruncate
import LevyStochCalc.Poisson.CharacterCompensator
import LevyStochCalc.Poisson.CharacterStrict
import LevyStochCalc.Poisson.CharacterCell
import LevyStochCalc.Poisson.CharacterStrictProcess
import LevyStochCalc.Poisson.CharacterMarkFactor
import LevyStochCalc.Probability.PredictableContinuous
import LevyStochCalc.Poisson.CellIntegrand
import LevyStochCalc.Poisson.CharacterFubini
import LevyStochCalc.Poisson.CharacterGronwall
import LevyStochCalc.Poisson.CharacterVanish
import LevyStochCalc.Poisson.PredictableRepresentation
import LevyStochCalc.Poisson.Filtered
import LevyStochCalc.Poisson.IndependentScattering
import LevyStochCalc.Poisson.MathFinBridge
import LevyStochCalc.Poisson.NaturalFiltration
import LevyStochCalc.Poisson.CylinderCharacters
import LevyStochCalc.Poisson.CompensatedIntegrandComplete
import LevyStochCalc.Poisson.CompensatedLinear
import LevyStochCalc.Poisson.CompensatedRange
import LevyStochCalc.Poisson.CompensatedPullOut
import LevyStochCalc.Poisson.CompensatedSimple
import LevyStochCalc.Poisson.CompensatedIsometry
import LevyStochCalc.Poisson.CompensatedMartingale
import LevyStochCalc.Poisson.CompensatedDensity
import LevyStochCalc.Poisson.MarkStep
import LevyStochCalc.Poisson.CompensatedApprox
import LevyStochCalc.Poisson.CompensatedProcess
import LevyStochCalc.Poisson.CompensatedQuadVar
import LevyStochCalc.Poisson.CompensatedProcessQuadVar
import LevyStochCalc.Poisson.CompensatedDiff
import LevyStochCalc.Poisson.Compensated
import LevyStochCalc.Poisson.CompensatedCongr
import LevyStochCalc.Poisson.PredictableIntegrand
import LevyStochCalc.Poisson.PerpBridge

-- Layer 0.5: martingale path regularity (càdlàg modifications)
import LevyStochCalc.Martingale.RightCont
import LevyStochCalc.Martingale.BDGTwo
import LevyStochCalc.Martingale.CadlagModification
import LevyStochCalc.Martingale.SquareCompensator

-- Layer 1: Itô-Lévy isometry  → I02
import LevyStochCalc.Poisson.L2Isometry

-- Layer 1.5: Brownian motion (existence via RemyDegenne/brownian-motion)
import LevyStochCalc.Brownian.Construction
import LevyStochCalc.Brownian.Existence
import LevyStochCalc.Brownian.Continuity
import LevyStochCalc.Brownian.Martingale
import LevyStochCalc.Brownian.Filtered
import LevyStochCalc.Brownian.MultidimFiltered
import LevyStochCalc.Brownian.LinearCombination
import LevyStochCalc.Brownian.ItoDriverLinear
import LevyStochCalc.Brownian.PRPMultidim
import LevyStochCalc.Brownian.PRPBrownian
import LevyStochCalc.Brownian.CylinderCharacters
import LevyStochCalc.Brownian.Multidim
import LevyStochCalc.Brownian.Transport
import LevyStochCalc.Poisson.Transport
import LevyStochCalc.Driver.Joint
import LevyStochCalc.Driver.JointCharacters
import LevyStochCalc.Driver.JointFiltration
import LevyStochCalc.Driver.ProductRule
import LevyStochCalc.Driver.CellPairing
import LevyStochCalc.Driver.CellIdentity
import LevyStochCalc.Driver.CellFubini
import LevyStochCalc.Driver.CellGronwall
import LevyStochCalc.Driver.CellComplex
import LevyStochCalc.Driver.JointGrid
import LevyStochCalc.Driver.JointMultidim
import LevyStochCalc.Driver.JointComplement
import LevyStochCalc.Driver.CrossFiltration
import LevyStochCalc.Driver.CrossElementary
import LevyStochCalc.Driver.CrossSimple
import LevyStochCalc.Driver.CrossOrthogonality
import LevyStochCalc.Driver.JointRange
import LevyStochCalc.Driver.JointPRP
import LevyStochCalc.Driver.JointPRPDegenerate
import LevyStochCalc.Driver.PredictableRepresentation
import LevyStochCalc.Driver.RightContIncrement
import LevyStochCalc.Driver.Existence
import LevyStochCalc.Driver.VectorIncrement
import LevyStochCalc.Driver.GridIncrement
import LevyStochCalc.Driver.ValueSigma
import LevyStochCalc.Driver.GermIndep
import LevyStochCalc.Driver.CadlagMartingale
import LevyStochCalc.Brownian.ItoSimple
import LevyStochCalc.Brownian.ItoDensity
import LevyStochCalc.Brownian.ItoMartingale
import LevyStochCalc.Brownian.SimplePredictableRefine
import LevyStochCalc.Brownian.ItoL2Completion
import LevyStochCalc.Brownian.ItoLinear
import LevyStochCalc.Brownian.ItoIntegrandComplete
import LevyStochCalc.Brownian.ItoRange
import LevyStochCalc.Brownian.PredictableIntegrand
import LevyStochCalc.Brownian.ItoAlgebra
import LevyStochCalc.Brownian.ItoIncrement
import LevyStochCalc.Brownian.ItoTrigIncrement
import LevyStochCalc.Brownian.ItoPullOut
import LevyStochCalc.Brownian.LeftFreeze
import LevyStochCalc.Brownian.CellCharacter
import LevyStochCalc.Brownian.PRPPairing
import LevyStochCalc.Brownian.PRPCell
import LevyStochCalc.Brownian.PRPGrid
import LevyStochCalc.Brownian.ItoFourthMoment
import LevyStochCalc.Brownian.ItoIncrementMoment
import LevyStochCalc.Brownian.ItoQuadVarSum
import LevyStochCalc.Brownian.DriftIncrement
import LevyStochCalc.Brownian.ItoFormula
import LevyStochCalc.Brownian.ItoFormulaGrid
import LevyStochCalc.Brownian.ItoGridPartition
import LevyStochCalc.Brownian.ItoMartingaleRiemann
import LevyStochCalc.Brownian.ItoQuadVarRiemann
import LevyStochCalc.Brownian.ItoFormulaScalar
import LevyStochCalc.Brownian.AugmentedFiltration
import LevyStochCalc.Brownian.ItoVersionExists
import LevyStochCalc.Brownian.ItoProcess
import LevyStochCalc.Brownian.ItoProcessVersion
import LevyStochCalc.Brownian.ItoProcessWindow
import LevyStochCalc.Brownian.ItoTimeRiemann
import LevyStochCalc.Brownian.ItoRiemannIntegrand
import LevyStochCalc.Brownian.RiemannSum
import LevyStochCalc.Brownian.TaylorTwo
import LevyStochCalc.Brownian.TaylorTwoVector
import LevyStochCalc.Brownian.TaylorTwoTime
import LevyStochCalc.Brownian.TaylorTwoModulus
import LevyStochCalc.Probability.MartingaleDifference
import LevyStochCalc.Brownian.MultidimIto
import LevyStochCalc.Brownian.CrossOrthogonality
import LevyStochCalc.Brownian.PRPMultidimRange
import LevyStochCalc.Brownian.PRPPerpBridge
import LevyStochCalc.Brownian.PRPMultidimAssembly

-- Layer 2: Itô-Lévy formula  → Cu03
import LevyStochCalc.Ito.Setting
import LevyStochCalc.Ito.Picard
import LevyStochCalc.Ito.PicardIntegrand
import LevyStochCalc.Ito.PicardSpace
import LevyStochCalc.Ito.PicardOutput
import LevyStochCalc.Ito.PicardLimit
import LevyStochCalc.Ito.PicardContraction
import LevyStochCalc.Ito.PicardSupL2
import LevyStochCalc.Ito.PicardLocality
import LevyStochCalc.Ito.PicardWindow
import LevyStochCalc.Ito.PicardGlobal
import LevyStochCalc.Ito.PicardWellPosed
import LevyStochCalc.Ito.PicardFixedPoint
import LevyStochCalc.Ito.JumpFormula

-- Layer 3 (+ 3a): BSDEJ existence  → Cu01
import LevyStochCalc.BSDEJ.Definition
import LevyStochCalc.BSDEJ.MartingaleRepresentation
import LevyStochCalc.BSDEJ.Existence

-- Layer 4: BSDEJ path regularity  → Cu05
import LevyStochCalc.BSDEJ.PathRegularity

/-!
# LevyStochCalc — root aggregator

Bottom-up continuous-time Lévy / jump stochastic calculus formalisation, written
to discharge the four cited continuous-time axioms of the main dissertation
(`D:/Dissertation/Dissertation/Continuous.lean`):

* `I02`  — Itô-Lévy L² isometry (Applebaum 2009 Thm 4.2.3)
* `Cu01` — Continuous BSDEJ existence/uniqueness (Tang-Li 1994)
* `Cu03` — Itô-Lévy formula for jump diffusions (Applebaum 2009 Thm 4.4.7)
* `Cu05` — BSDEJ path regularity (Bouchard-Elie 2008 SPA 118(1) pp 53-75 Thm 2.1;
  correcting the previous fabricated "Bouchard-Elie-Touzi 2009 SPA 119(11)"
  citation flagged by red-team 1st audit P11 + 2nd audit P10)

Each layer below targets one cited result (or builds machinery used by the next layer).
Every module is complete: `tools/sorry_baseline.txt` is empty and the only `axiom`
declaration is cited axiom #16 (`Ito/JumpFormula.lean`, `tools/cited_axioms.md`).
-/
