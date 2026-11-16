import Lax369799Proofs.ClosedExtremal
import Lax369799Proofs.ExtendedContexts
import Lax369799Proofs.ModalAcceptanceGame
import Lax369799Proofs.ParityGameEquations
import Lax369799Proofs.MainTheorems
import Lax369799Proofs.FiniteMuEquations
import Lax369799Proofs.ModalTransitions
import Lax369799Proofs.CloneNormalization
import Lax369799Proofs.AlgebraicBranchCondition
import Lax369799Proofs.FiniteParityGames
import Lax369799Proofs.UnaryChains
import Lax369799Proofs.AlgebraToAutomaton
import Lax369799Proofs.CloneTransitions
import Lax369799Proofs.DirectionReindexing
import Lax369799Proofs.SupportCompaction
import Lax369799Proofs.PriorityCompilation

-- Each endpoint below must use only propext, Classical.choice, and Quot.sound.
#print axioms Lax369799Proofs.WordAutomata.buchiDeterminization
#print axioms Lax369799Proofs.WordAutomata.FinGame.Arena.determined
#print axioms Lax369799Proofs.OmegaDeterminization.determinization
#print axioms Lax369799Proofs.FiniteParityGames.positional_determinacy
#print axioms Lax369799Proofs.AlgebraicOmegaWords.regular
#print axioms Lax369799Proofs.AlgebraicBranchCondition.exists_condition
#print axioms Lax369799Proofs.UnaryChains.word_evaluation
#print axioms Lax369799Proofs.UnaryGraphEvaluation.agreement
#print axioms Lax369799Proofs.UnarySystemEvaluation.agreement
#print axioms Lax369799Proofs.RunAcceptance.evaluated_run_iff
#print axioms Lax369799Proofs.AlgebraToAutomaton.algebra_to_automaton
#print axioms Lax369799Proofs.CloneTransitions.clone_automaton
#print axioms Lax369799Proofs.CloneTransitions.uniform_stabilization
#print axioms Lax369799Proofs.DirectionReindexing.decode_isomorphic

#print axioms Lax369799Proofs.CloneNormalization.bisim_automaton_exists
#print axioms Lax369799Proofs.RunAcceptance.labelling_accepting
#print axioms Lax369799Proofs.BranchMonotonicity.infinite_mono
#print axioms Lax369799Proofs.CloneRunRefinement.run_refinement

#print axioms Lax369799Proofs.CloneNormalization.bisim_automaton_runs
#print axioms Lax369799Proofs.FiniteMuEquations.solve_correct
#print axioms Lax369799Proofs.ModalTransitions.eval_transition
#print axioms Lax369799Proofs.ModalTransitions.run_marking

-- Both main results now close without paper-statement axioms.
#print axioms Lax369799Proofs.MainTheorems.algebra_to_mu
#print axioms Lax369799Proofs.MainTheorems.finite_bisimulation_invariant_mso

#print axioms Lax369799Proofs.ClosedExtremal.witness_value

#print axioms Lax369799Proofs.ClosedExtremal.normal_test

#print axioms Lax369799Proofs.ExtremalSituations.normal_test

#print axioms Lax369799Proofs.ExtendedContexts.normal_test

#print axioms Lax369799Proofs.ParityWinningRegions.predecessor

#print axioms Lax369799Proofs.ModalAcceptanceGame.predecessor

#print axioms Lax369799Proofs.ModalAcceptanceGame.reverse_parity

#print axioms Lax369799Proofs.ModalAcceptanceGame.terminal_winning

#print axioms Lax369799Proofs.ModalAcceptanceGame.winning_equation

#print axioms Lax369799Proofs.ParityFixedPoints.greatest

#print axioms Lax369799Proofs.ParityFixedPoints.least

#print axioms Lax369799Proofs.ParityGameEquations.winning

#print axioms Lax369799Proofs.ModalAcceptanceGame.winning_nested

#print axioms Lax369799Proofs.FixedPointRetraction.least
#print axioms Lax369799Proofs.FixedPointRetraction.greatest
#print axioms Lax369799Proofs.ModalGameEquations.winning
#print axioms Lax369799Proofs.ModalGameTranslation.game_to_mu
#print axioms Lax369799Proofs.AutomatonRunGame.run_winning
#print axioms Lax369799Proofs.CloneGameRun.winning_run
#print axioms Lax369799Proofs.BisimAutomatonTheorem.bisim_automaton_to_mu
#print axioms Lax369799Proofs.SupportCompaction.compact_exists
#print axioms Lax369799Proofs.SupportCompaction.rename_supported_iff
#print axioms Lax369799Proofs.PriorityCompilation.compile_correct
#print axioms Lax369799Proofs.PriorityCompilation.sentence_correct
