# AI-use statement

I used two AI tools on this project: ChatGPT (OpenAI) and Claude (Anthropic).

Most of the work is mine. I chose the topic and the approach, and Checkpoint1.lean, Checkpoint2.lean, Checkpoint34.lean (checkpoints 1 to 4) and ResearchNotes.lean are my own work. In the remaining Lean files, ChatGPT drafted skeletons of the proofs, and for the harder proofs it gave hints after I had isolated the difficult step as a black box. Four proofs are mostly AI-written, namely
`countable_below_of_strictly_cofinal_chain`, `ambient_no_cofinal_chain`,
`not_countable_below_omega_one` and `family_countable_of_coloring_and_countable_antichains`. Claude was used only for build fixes and for editing text. Section 5 lists every declaration where AI-written code remains.

## 1. Tools and models

- **ChatGPT (OpenAI).** Model: GPT-6 High. Used for exploring approaches, drafting proof skeletons and
  hints, debugging, and documentation. Used throughout the semester.
- **Claude (Anthropic).** Model: `claude-sonnet-5-5` (Claude Sonnet 5.5), as configured for the
  session. The model serving a given turn can differ from the configured one. Used for diagnosing
  and fixing the build and for editing report and README text, from November 16 to 23, 2026.


## 2. My own contribution

- I chose the topic, motivated by my coursework in set theory and my interest in formalizing
  material that is not readily available in Mathlib, and I chose the rational-sequence approach.
  I also met with Prof. Sumun Iyer to discuss the scope, approaches, and extensions toward Suslin
  trees (see `COLLABORATION.md`).
- I wrote the course-checkpoint files (`Checkpoint1.lean`, `Checkpoint2.lean`,
  `Checkpoint34.lean`) and `ResearchNotes.lean` myself, as the commit history shows. These contain
  the core definitions (`RationalNode`, `EndExtends`, and the related notions) and my exploratory
  notes and comments.
- I made the final design decisions, informed by course-staff feedback about unnecessary custom
  definitions and bundled hypotheses.
- I ran every AI-suggested proof through Lean and the project build, and I checked every Mathlib
  declaration an AI pointed me to.
- I wrote the actual substance of the report. Its reflection section is based on my own Lean comments
  and notes.

## 3. ChatGPT

**Project development and mathematical background.** I used ChatGPT to weigh and discuss my own ideas for formalizing Aronszajn trees in Lean 4, in particular the construction with strictly increasing rational-valued sequences indexed by countable ordinals. It helped me compare representations of trees, understand the role of ordinal heights and well-founded orders, and
investigate how Aronszajn, special, and Suslin trees relate. It also helped me identify the countable limit-ordinal step as the central difficulty and suggested ways to organize the remaining proof obligations. The choice of topic and approach was mine.
 
**Definitions and formalization design.** I wrote all of the definitions and theorem statements myself, including the core definitions in my checkpoint files and the later ones such as `appendRational`, `initialSegmentsFamily`, and the statement of `aronszajn_of_extension_invariant`. ChatGPT did not write any of them. It discussed design alternatives with me and helped me locate Mathlib declarations (for example `WellFounded.rank`, `StrictMono`, `IsChain`, and countability lemmas) alongside my own reading and web search. I checked all of these myself afterwards. I also asked it whether any of my definitions could be replaced by existing Mathlib abstractions, in case I had missed redundant parts of my own work.
 
**Proof development and debugging.** In every Lean file other than my checkpoint files and `ResearchNotes.lean`, that is `OrdinalHeights.lean`, `ConstructionOrder.lean`, `NoCofinalBranch.lean`, `LevelConstruction.lean`, `SpecialTrees.lean` and `FinalCriterion.lean`, ChatGPT drafted the skeleton of each proof, and I filled in most of the skeletons myself. Four of the proofs are mostly AI-written, and section 5 names them. I tried to write each of the other proofs on my own first. When I ran into problems, I consulted ChatGPT, and I then kept experimenting myself until `lake build` succeeded. For the harder proofs, I first isolated the difficult step as a black box, and ChatGPT then gave me hints toward filling it in. ChatGPT also
helped me interpret compiler errors, suggested alternative proof strategies when I asked, and pointed me to relevant Mathlib lemmas. When I had trouble reading the infoview, I sometimes discussed errors and their mathematical meaning with it.
 
**Documentation.** ChatGPT helped me improve my explanatory comments, documentation, and GitHub organizatio and gave me the basic skeleton of the report according to the course project guidelines.
 

## 4. Claude
- Diagnosed the failing `lake build`. It found invalid Mathlib names at the pinned version (`Ordinal.cardinalMk_Iio`, an unqualified `lt_succ`) and, using my build output, fixed the remaining type errors.
- Claude did not write the definitions, theorem statements, or main proofs of the project. Its changes to Lean files were the build fixes listed in section 5.


## 5. Files and theorems where AI wrote or substantially rewrote code that remains
 
**Mostly AI-written proofs.** For these four, most of the proof text that remains came from AI,
not from me. I checked each one in Lean.
 
- `NoCofinalBranch.lean`: `countable_below_of_strictly_cofinal_chain` and
  `ambient_no_cofinal_chain`.
- `NoCofinalBranch.lean`: the private theorem `not_countable_below_omega_one`. The first version used a Mathlib lemma that does not exist and Claude rewrote the proof.
- `SpecialTrees.lean`: `family_countable_of_coloring_and_countable_antichains`.
**Proof skeletons.** ChatGPT drafted a proof skeleton for every theorem below, and I filled in the skeletons, apart from the four above. I list them all because I think that skeletons that remain in the repository count as AI-generated code.
 
- `OrdinalHeights.lean`: `endExtends_eq_restrict`, `initialSegments_eq_of_length_eq`,
  `comparable_eq_of_length_eq`.
- `ConstructionOrder.lean`: `endExtends_eq_of_length_eq`, `endExtends_antisymm`,
  `length_lt_of_lt`, `rationalNodes_form_tree`.
- `NoCofinalBranch.lean`: `countable_below_of_strictly_cofinal_chain`, `ambient_no_cofinal_chain`,
  `selected_family_no_cofinal_chain`, `aronszajn_of_height_and_countable_levels`.
- `LevelConstruction.lean`: `endExtends_appendRational`, `successor_extension_with_room`,
  `initialSegmentsFamily_level_subsingleton`, `initialSegmentsFamily_countable_levels`,
  `initialSegmentsFamily_nonempty_below`, `nonempty_levels_of_extension_invariant`.
- `SpecialTrees.lean`: `chain_countable_of_antichain_coloring`,
  `family_countable_of_coloring_and_countable_antichains`, `uncountable_special_not_suslin`.
- `FinalCriterion.lean`: `aronszajn_of_extension_invariant`.

**Hints.** For the harder proofs in the lists above, I first black-boxed the difficult step, and ChatGPT then gave me hints toward filling it in.
 
Claude changed the following code that remains in the repository:
- `NoCofinalBranch.lean`, `not_countable_below_omega_one`: Claude rewrote the proof.
- `NoCofinalBranch.lean`, `countable_below_of_strictly_cofinal_chain`: fixed one `calc` step.
- `NoCofinalBranch.lean`, `ambient_no_cofinal_chain`: `Order.lt_succ` in place of `lt_succ`.
- `LevelConstruction.lean`, `appendRational` and `nonempty_levels_of_extension_invariant`: fixed
  one line in each.
- `SpecialTrees.lean`, `chain_countable_of_antichain_coloring`: fixed one line.

The files `Checkpoint1.lean`, `Checkpoint2.lean`, `Checkpoint34.lean` and `ResearchNotes.lean` are my own work.

## 6. Verification
I used Lean's compiler and the project build (`lake build`, and the GitHub Actions run) to test all AI-assisted code. I am well aware that compilation is an important check on the formal statements and proofs, but it does not by itself show that the formalized statements express every aspect of the intended
mathematics.

This statement is meant to acknowledge the full extent of AI assistance in both the formalization and its documentation.