A Formalized Reduction of Keller's Conjecture
==
Installation (from repository)
--
* First, install Lean and VS Code following these [instructions](https://leanprover-community.github.io/get_started.html).
* Then you can either:
    * Run the following to let leanproject clone and build the repository automatically:
      ```
      $ leanproject get https://github.com/JOSHCLUNE/Keller_reduction.git 
      ```
    * or manually run:
      ```
      $ git clone https://github.com/JOSHCLUNE/Keller_reduction.git 
      $ cd Keller_reduction
      $ leanproject build
      ```
Installation (from zip file)
--
* First, install Lean and VS Code following these [instructions](https://leanprover-community.github.io/get_started.html).
* Then, navigate to the top level directory and run `leanproject build`

Editing
--
To inspect and modify our proofs, install [Visual Studio Code](https://code.visualstudio.com/) or `emacs` with the Lean extension. This will allows you to inspect the proof states in tactic proofs.

To recompile/typecheck the project after making edits, simply run `leanproject build`.

Note that if any edits are made to `verified_clique.lean` or `keller_graphs.lean` (which `verified_clique.lean` depends on), then `leanproject build` will need to rebuild `verified_clique.olean` which may take up to half an hour. Recompiling/typechecking other files should not take nearly as much time.

Relation to the paper
--
This section is included to help readers find various lemmas/theorems/definitions from the paper in the codebase.
* `point` is defined in `helpers.lean`
* `in_cube`, `cube`, `is_tiling`, `is_facesharing`, and `tiling_faceshare_free` are defined in `cube_tilings.lean`
* `Keller_conjecture` is defined in `periodic_reduction.lean`
* `Keller_conjecture_false`, which shows that Keller's conjecture does not hold in 8 dimensions, is proven in `keller_implies_no_clique.lean`
* `Keller_graph` and `has_clique` are defined in `keller_graphs.lean`
* `clique_existence_refutes_Keller_conjecture` implements Theorem 3 and is proven in `keller_implies_no_clique.lean`
* `clique_nonexistence_implies_Keller_conjecture` implements the contrapositive of Theorem 7 and is proven in `no_clique_implies_keller.lean`
* Lemma 1 is implemented as `tiling_lattice_structure` in `tilings_structure.lean`
* Definition 1 is represented as `is_periodic` in `periodic_tilings.lean`
* Definitions 2 and 3 don't have direct representations in the codebase, but Definition 4 is represented as `has_periodic_core` in `periodic_tilings.lean`
* `is_periodic_of_has_periodic_core` and `has_periodic_core_of_is_periodic` are defined in `periodic_tilings.lean`
* Lemma 2 is implemented as `periodic_reduction` in `periodic_reduction.lean`
* Lemma 2.1 is implemented as `T'_is_tiling` in `periodic_reduction.lean`
* Lemma 2.2 is implemented as `T'_faceshare_free` in `periodic_reduction.lean`
* Lemma 3.1 is implemented as `tiling_from_clique_is_tiling` in `keller_implies_no_clique.lean`
* Definition 5 is represented as `cubelet` in `keller_implies_no_clique.lean`
* Definition 6 is represented as `valid_core_cubelet` in `keller_implies_no_clique.lean`
* Lemma 3.2 is implemented as `tiling_from_clique_faceshare_free` in `keller_implies_no_clique.lean`
* Definition 8 is represented as `is_s_discrete` in `s_discrete.lean`
* `shift` is implemented as `shift_tiling` in `tilings_structure.lean`
* Definition 7, Lemma 4, Lemma 4.1, and Lemma 5 do not have exact analogs in the codebase because the presentation of this portion of the proof in the paper omitted/simplified some details for the sake of clarity.
    * The closest analog to Lemma 4 is `inductive_replacement_lemma` in `no_clique_implies_keller.lean`
    * The closest analog to Lemma 4.1 is `replacement_lemma` in `tilings_structure.lean`, though the additional reasoning about tilings being s-discrete is done in `inductive_replacement_lemma`
    * The closest analog to Lemma 5 is the construction of `goal_clique` defined in `periodic_tiling_implies_clique` in `no_clique_implies_keller.lean`
* Lemma 6 is implemented as `s_discrete_upper_bound` in `s_discrete.lean`
* The clique verification described in section 5 is implemented in `verified_clique.lean`, culminating in the final theorem `G_8_2_has_clique` which is used to prove `Keller_conjecture_false` in `keller_implies_no_clique.lean`

Carneiro's Clique Verification
--

In Section 5.3 of the paper, we reference an alternative verification of the G_8 clique. This verification is included in the `Lean4_Clique` directory. Specifically, it is included in `Lean4_Clique/Clique/Clique.lean`. Note that unlike the rest of our code, this verification is implemented in Lean 4, rather than Lean 3.

To compile and edit this code, follow the instructions [here](https://leanprover.github.io/lean4/doc/quickstart.html) and run `lake build` from the `Lean4_Clique/Clique` directory. After the code has been compiled, it should be possible to view and edit it using Visual Studio Code's Lean 4 extension.
