(* Hall Theorem for countable families of finite sets
   Fabian Fernando Serrano Suárez  UNAL Manizales
   Thaynara Arielly de Lima        Universidade Federal de Goiáis 
   Mauricio Ayala-Rincón           Universidade de Brasília
*) 
theory Hall_Theorem
  imports  
   "Compactness"
   "Marriage.Marriage" 
begin

 definition system_representatives :: "('a ⇒ 'b set) ⇒ 'a set ⇒ ('a ⇒ 'b) ⇒ bool" where
"system_representatives S I R  ≡ (∀i∈I. (R i) ∈ (S i)) ∧ (inj_on R I)"

definition set_to_list :: "'a set ⇒ 'a list"
  where "set_to_list s =  (SOME l. set l = s)"

lemma  set_set_to_list:
   "finite s ⟹ set (set_to_list s) = s"
  unfolding set_to_list_def by (metis (mono_tags) finite_list some_eq_ex)

lemma list_to_set:
  assumes "finite (S i)"
  shows "set (set_to_list (S i)) = (S i)" 
  using assms  set_set_to_list  by auto

primrec disjunction_atomic :: "'b list ⇒'a ⇒ ('a × 'b)formula"  where
 "disjunction_atomic [] i = FF"   
| "disjunction_atomic (x#D) i = (atom (i, x)) ∨. (disjunction_atomic D i)"

lemma t_v_evaluation_disjunctions1:
  assumes "t_v_evaluation I (disjunction_atomic (a # l) i) = Ttrue"
  shows "t_v_evaluation I (atom (i,a)) = Ttrue ∨ t_v_evaluation I (disjunction_atomic l i) = Ttrue" 
proof-
  have
  "(disjunction_atomic (a # l) i) = (atom (i,a)) ∨. (disjunction_atomic l i)"
    by auto
  hence "t_v_evaluation I ((atom (i ,a)) ∨. (disjunction_atomic l i)) = Ttrue" 
    using assms by auto
  thus ?thesis using DisjunctionValues by blast
qed

lemma t_v_evaluation_atom:
  assumes "t_v_evaluation I (disjunction_atomic l i) = Ttrue"
  shows "∃x. x ∈ set l ∧ (t_v_evaluation I (atom (i,x)) = Ttrue)"
proof-
  have "t_v_evaluation I (disjunction_atomic l i) = Ttrue ⟹
  ∃x. x ∈ set l ∧ (t_v_evaluation I (atom (i,x)) = Ttrue)"
  proof(induct l)
    case Nil
    then show ?case by auto
  next   
    case (Cons a l)  
    show  "∃x. x ∈ set (a # l) ∧ t_v_evaluation I (atom (i,x)) = Ttrue"  
    proof-
      have
      "(t_v_evaluation I (atom (i,a)) = Ttrue) ∨ t_v_evaluation I (disjunction_atomic l i)=Ttrue" 
        using Cons(2) t_v_evaluation_disjunctions1[of I] by auto      
      thus ?thesis
    proof(rule disjE)
      assume "t_v_evaluation I (atom (i,a)) = Ttrue"
      thus ?thesis by auto
    next
      assume "t_v_evaluation I (disjunction_atomic l i) = Ttrue" 
      thus ?thesis using Cons by auto    
    qed
  qed
qed
  thus ?thesis using assms by auto
qed

definition ℱ :: "('a ⇒ 'b set) ⇒ 'a set ⇒ (('a × 'b)formula) set"  where
   "ℱ S I  ≡ (⋃i∈I. { disjunction_atomic (set_to_list (S i)) i })"

definition 𝒢 :: "('a ⇒ 'b set) ⇒ 'a set ⇒ ('a × 'b)formula set"  where
   " 𝒢 S I ≡ {¬.(atom (i,x) ∧. atom(i,y))
                         |x y i . x∈(S i) ∧ y∈(S i) ∧  x≠y ∧ i∈I}"

definition ℋ :: "('a ⇒ 'b set) ⇒ 'a set ⇒('a × 'b)formula set"  where
   "ℋ S I ≡ {¬.(atom (i,x) ∧. atom(j,x))
                         | x i j. x ∈ (S i) ∩ (S j) ∧ (i∈I ∧ j∈I ∧ i≠j)}"

definition 𝒯 :: "('a ⇒ 'b set) ⇒ 'a set ⇒ ('a × 'b)formula set"  where
   "𝒯 S I  ≡ (ℱ S I) ∪ (𝒢 S I) ∪ (ℋ S I)" 

primrec indices_formula :: "('a × 'b)formula  ⇒ 'a set" where
  "indices_formula FF = {}"
| "indices_formula TT = {}"
| "indices_formula (atom P) =  {fst P}"
| "indices_formula (¬. F) = indices_formula F"
| "indices_formula (F ∧. G) = indices_formula F ∪ indices_formula G"
| "indices_formula (F ∨. G) = indices_formula F ∪ indices_formula G"
| "indices_formula (F →. G) = indices_formula F ∪ indices_formula G"

definition  indices_set_formulas :: "('a × 'b)formula set  ⇒ 'a set" where
"indices_set_formulas S = (⋃F∈ S. indices_formula F)"

lemma finite_indices_formulas:
  shows "finite (indices_formula F)"
  by(induct F, auto)

lemma finite_set_indices:
  assumes  "finite S"
  shows "finite (indices_set_formulas S)" 
 using `finite S` finite_indices_formulas 
  by(unfold indices_set_formulas_def, auto)

lemma indices_disjunction:
  assumes "F = disjunction_atomic L  i" and "L ≠ []"
  shows "indices_formula F = {i}" 
proof-
  have  "(F = disjunction_atomic L  i  ∧  L ≠ []) ⟹ indices_formula F = {i}"
  proof(induct L arbitrary: F)
    case Nil hence False using assms by auto
    thus ?case by auto
  next
    case(Cons a L)
    assume "F = disjunction_atomic (a # L) i ∧ a # L ≠ []" 
    thus ?case
    proof(cases L)
      assume "L = []"                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         
      thus "indices_formula F = {i}" using Cons(2) by auto
    next
      show
  "⋀b list. F = disjunction_atomic (a # L) i ∧ a # L ≠ [] ⟹ L = b # list ⟹ 
            indices_formula F = {i}" 
        using Cons(1-2) by auto
    qed
  qed 
  thus ?thesis using assms  by auto
qed    

lemma nonempty_set_list:
  assumes "∀i∈I. (S i)≠{}" and "∀i∈I. finite (S i)"     
  shows "∀i∈I. set_to_list (S i)≠[]"  
proof(rule ccontr)
  assume "¬ (∀i∈I. set_to_list (S i) ≠ [])" 
  hence "∃i∈I. set_to_list (S i) = []" by auto 
  hence "∃i∈I. set(set_to_list (S i)) = {}" by auto
  then obtain i where i: "i∈I" and  "set (set_to_list (S i)) = {}" by auto
  thus False using list_to_set[of S i]  assms by auto
qed

lemma  at_least_subset_indices:
  assumes "∀i∈I. (S i)≠{}" and "∀i∈I. finite (S i)"  
  shows  "indices_set_formulas (ℱ S I) ⊆ I" 
proof
  fix i
  assume hip: "i ∈ indices_set_formulas (ℱ S I)" show  "i ∈ I"
  proof-  
    have "i ∈ (⋃F∈(ℱ S I). indices_formula F)" using hip
      by(unfold indices_set_formulas_def,auto)
    hence "∃F ∈ (ℱ S I). i ∈ indices_formula F" by auto
    then obtain F where "F∈(ℱ S I)" and i: "i ∈ indices_formula F" by auto
    hence "∃ k∈I. F = disjunction_atomic (set_to_list (S k)) k"
      by (unfold ℱ_def, auto) 
    then obtain k where
    k: "k∈I" and "F = disjunction_atomic (set_to_list (S k)) k" by auto
    hence "indices_formula F = {k}"
      using assms  nonempty_set_list[of I S] 
      indices_disjunction[OF `F = disjunction_atomic (set_to_list (S k))  k`]
      by auto
    hence "k = i" using i by auto
    thus ?thesis using k by auto
  qed
qed

lemma at_most_subset_indices:
  shows "indices_set_formulas (𝒢 S I) ⊆ I"
proof
  fix i
  assume hip: "i ∈ indices_set_formulas (𝒢 S I)" show  "i ∈ I"
  proof-
    have "i ∈ (⋃F∈(𝒢 S I). indices_formula F)" using hip
      by(unfold indices_set_formulas_def,auto)
    hence "∃F∈(𝒢 S I). i ∈ indices_formula F" by auto
    then obtain F where "F∈(𝒢 S I)" and i: "i ∈ indices_formula F"
      by auto
    hence "∃x y j. x∈(S j) ∧ y∈(S j) ∧ x≠y ∧ j∈I ∧ F = 
           ¬.(atom (j, x) ∧. atom(j,y))"
      by (unfold 𝒢_def, auto)
    then obtain x y j where "x∈(S j) ∧ y∈(S j) ∧ x≠y ∧ j∈I"
      and "F = ¬.(atom (j, x) ∧. atom(j,y))"
      by auto
    hence "indices_formula F = {j} ∧ j∈I" by auto
    thus "i ∈ I" using i by auto
  qed
qed

lemma  different_subset_indices:
  shows "indices_set_formulas (ℋ S I) ⊆ I" 
proof
  fix i
  assume hip: "i ∈ indices_set_formulas (ℋ S I)" show "i ∈ I"
  proof-
    have "i ∈ (⋃F∈(ℋ S I). indices_formula F)" using hip
      by(unfold indices_set_formulas_def,auto)
    hence "∃F∈(ℋ S I) . i ∈ indices_formula F" by auto
    then obtain F where "F∈(ℋ S I)" and i: "i ∈ indices_formula F"
      by auto
    hence "∃ x j k. x ∈ (S j) ∩ (S k) ∧ (j∈I ∧ k∈I ∧ j≠k) ∧ F =
           ¬.(atom (j,x) ∧. atom(k,x))"
      by (unfold ℋ_def, auto)
    then obtain x j k
      where "(j∈I ∧ k∈I ∧ j≠k) ∧ F = ¬.(atom (j, x) ∧. atom(k,x))"
      by auto
    hence u: "j∈I" and v: "k∈I" and "indices_formula F = {j,k}"
      by auto
    hence "i=j ∨ i=k"  using i by auto
    thus "i ∈ I" using u v  by auto
  qed
qed

lemma indices_union_sets:
  shows "indices_set_formulas(A ∪ B) = (indices_set_formulas A) ∪ (indices_set_formulas B)"
   by(unfold  indices_set_formulas_def, auto)

lemma at_least_subset_subset_indices1:
  assumes "F∈(ℱ S I)"
  shows "(indices_formula F) ⊆ (indices_set_formulas (ℱ S I))"
proof
  fix i 
  assume hip: "i ∈ indices_formula F"
  show  "i ∈ indices_set_formulas (ℱ S I)"
  proof-
    have "∃F. F∈(ℱ S I) ∧ i ∈ indices_formula F" using assms hip by auto
    thus  ?thesis by(unfold indices_set_formulas_def, auto)
  qed
qed 

lemma at_most_subset_subset_indices1:
  assumes  "F∈(𝒢 S I)"
  shows "(indices_formula F) ⊆ (indices_set_formulas (𝒢 S I))" 
proof
  fix i 
  assume hip: "i ∈ indices_formula F"
  show  "i ∈ indices_set_formulas (𝒢 S I)"
  proof-
    have "∃F. F∈(𝒢 S I) ∧ i ∈ indices_formula F" using assms hip by auto
    thus ?thesis by(unfold indices_set_formulas_def, auto)
  qed
qed

lemma different_subset_indices1:
  assumes  "F∈(ℋ S I)"
  shows "(indices_formula F) ⊆ (indices_set_formulas (ℋ S I))" 
proof
  fix i 
  assume hip: "i ∈ indices_formula F"
  show  "i ∈ indices_set_formulas (ℋ S I)"
  proof-
    have "∃F. F∈(ℋ S I) ∧ i ∈ indices_formula F" using assms hip by auto
    thus ?thesis by(unfold indices_set_formulas_def, auto)
  qed
qed

lemma all_subset_indices:
  assumes  "∀i∈I.(S i)≠{}" and "∀i∈I. finite(S i)"
  shows "indices_set_formulas (𝒯 S I) ⊆ I"
proof
  fix i
  assume hip: "i ∈ indices_set_formulas (𝒯 S I)" show "i ∈ I"
  proof-
    have  "i ∈ indices_set_formulas ((ℱ S I) ∪ (𝒢 S I)  ∪ (ℋ S I))"
      using hip by (unfold 𝒯_def,auto)
    hence "i ∈ indices_set_formulas ((ℱ S I) ∪ (𝒢 S I)) ∪
    indices_set_formulas(ℋ S I)"
      using indices_union_sets[of "(ℱ S I) ∪ (𝒢 S I)"] by auto
    hence "i ∈ indices_set_formulas ((ℱ S I) ∪ (𝒢 S I)) ∨ 
    i ∈ indices_set_formulas(ℋ S I)"
      by auto
    thus ?thesis
    proof(rule disjE)        
      assume hip: "i ∈ indices_set_formulas (ℱ S I ∪ 𝒢 S I)"       
      hence "i ∈ (⋃F∈ (ℱ S I) ∪ (𝒢 S I). indices_formula F)"
        by(unfold  indices_set_formulas_def, auto)
      then obtain F
      where F: "F∈(ℱ S I) ∪ (𝒢 S I)" and i: "i ∈ indices_formula F" by auto 
      from F have  "(indices_formula F) ⊆ (indices_set_formulas (ℱ S I))
      ∨ indices_formula F ⊆ (indices_set_formulas (𝒢 S I))"
        using at_least_subset_subset_indices1 at_most_subset_subset_indices1 by blast
      hence "i ∈ indices_set_formulas (ℱ S I) ∨
               i ∈ indices_set_formulas (𝒢 S I)"
        using i by auto
      thus "i ∈ I" 
        using assms at_least_subset_indices[of I S] at_most_subset_indices[of S I] by auto
      next
      assume "i ∈ indices_set_formulas (ℋ S I)" 
      hence
      "i ∈ (⋃F∈(ℋ S I). indices_formula F)" 
        by(unfold  indices_set_formulas_def, auto)
      then obtain F where F:  "F∈(ℋ S I)" and i: "i ∈ indices_formula F"
        by auto
      from F have "(indices_formula F) ⊆ (indices_set_formulas (ℋ S I))"
        using different_subset_indices1 by blast
      hence "i ∈ indices_set_formulas (ℋ S I)" using i by auto
      thus "i ∈ I" using different_subset_indices[of S I]
        by auto
    qed
  qed
qed

lemma inclusion_indices:
  assumes "S ⊆ H" 
  shows  "indices_set_formulas S ⊆ indices_set_formulas H" 
proof
  fix i
  assume "i ∈ indices_set_formulas S"
  hence "∃F. F ∈ S ∧ i ∈ indices_formula F"
    by(unfold indices_set_formulas_def, auto) 
  hence "∃F. F ∈ H ∧ i ∈ indices_formula F" using assms by auto
  thus  "i ∈ indices_set_formulas H" 
    by(unfold indices_set_formulas_def, auto)
qed

lemma indices_subset_formulas:
  assumes  "∀i∈I.(S i)≠{}" and "∀i∈I. finite(S i)" and "A ⊆ (𝒯 S I)" 
  shows "(indices_set_formulas A) ⊆ I" 
proof-
  have "(indices_set_formulas A) ⊆ (indices_set_formulas (𝒯 S I))"
    using assms(3) inclusion_indices by auto
  thus ?thesis using assms(1-2) all_subset_indices[of I S] by auto
qed

lemma To_subset_all_its_indices:
  assumes  "∀i∈I. (S i)≠{}" and "∀i∈I. finite (S i)" and  "To ⊆ (𝒯 S I)"
  shows "To ⊆ (𝒯 S (indices_set_formulas To))"
proof
  fix F
  assume hip: "F ∈ To" 
  hence "F ∈ (𝒯 S I)" using assms(3) by auto
  hence "F ∈ (ℱ S I) ∪ (𝒢 S I) ∪ (ℋ S I)" by(unfold 𝒯_def,auto)
  hence "F ∈ (ℱ S I) ∨ F ∈ (𝒢 S I) ∨ F ∈ (ℋ S I)" by auto
  thus "F∈(𝒯 S (indices_set_formulas To))"  
  proof(rule disjE)
    assume "F ∈ (ℱ S I)"
    hence "∃i∈I. F =  disjunction_atomic (set_to_list (S i)) i" 
      by(unfold ℱ_def,auto)
    then obtain i
      where i: "i∈I" and F: "F =  disjunction_atomic (set_to_list (S i)) i"
      by auto
    hence "indices_formula F = {i}"
      using 
      assms(1-2) nonempty_set_list[of I S] indices_disjunction[of F "(set_to_list (S i))" i ]
      by auto
    hence "i∈(indices_set_formulas To)" using hip
      by(unfold indices_set_formulas_def,auto)
    hence "F∈(ℱ S (indices_set_formulas To))" 
      using F by(unfold ℱ_def,auto)
    thus "F∈(𝒯 S (indices_set_formulas To))"
      by(unfold 𝒯_def,auto)
  next
    assume "F ∈ (𝒢 S I) ∨ F ∈ (ℋ S I)"
    thus ?thesis
    proof(rule disjE)
      assume "F ∈ (𝒢 S I)" 
      hence "∃x.∃y.∃i. F = ¬.(atom (i,x) ∧. atom(i,y)) ∧ x∈(S i) ∧
               y∈(S i) ∧  x≠y ∧ i∈I"
        by(unfold 𝒢_def, auto)
      then obtain x y i
        where F1: "F = ¬.(atom (i,x) ∧. atom(i,y))" and
                F2: "x∈(S i) ∧ y∈(S i) ∧  x≠y ∧ i∈I"
        by auto
      hence "indices_formula F = {i}" by auto
      hence "i∈(indices_set_formulas To)" using hip
        by(unfold indices_set_formulas_def,auto)
      hence "F∈(𝒢 S (indices_set_formulas To))"
        using F1 F2 by(unfold 𝒢_def,auto)
      thus "F∈(𝒯 S (indices_set_formulas To))"  by(unfold 𝒯_def,auto)
    next
      assume "F ∈ (ℋ S I)"
      hence "∃x.∃i.∃j. F = ¬.(atom (i,x) ∧. atom(j,x)) ∧ 
              x ∈ (S i) ∩ (S j) ∧ (i∈I ∧ j∈I ∧ i≠j)" 
        by(unfold  ℋ_def, auto)
      then obtain x i j
        where F3: "F = ¬.(atom (i,x) ∧. atom(j,x))" and 
                F4: " x ∈ (S i) ∩ (S j) ∧ (i∈I ∧ j∈I ∧ i≠j)" 
        by auto 
      hence "indices_formula F = {i,j}" by auto
      hence "i∈(indices_set_formulas To) ∧ j∈(indices_set_formulas To)" 
        using hip by(unfold indices_set_formulas_def,auto)
      hence "F∈(ℋ S (indices_set_formulas To))"
        using F3 F4 by(unfold ℋ_def,auto)
      thus "F∈(𝒯 S (indices_set_formulas To))"  by(unfold 𝒯_def,auto)
    qed
  qed
qed

lemma all_nonempty_sets:
  assumes  "∀i∈I. (S i)≠{}" and "∀i∈I. finite (S i)" and "A ⊆ (𝒯 S I)" 
  shows   "∀i∈(indices_set_formulas A). (S i)≠{}"
proof-
  have "(indices_set_formulas A)⊆I" 
    using assms(1-3) indices_subset_formulas[of I S A] by auto
  thus ?thesis using assms(1) by auto
qed

lemma all_finite_sets:
  assumes  "∀i∈I. (S i)≠{}" and "∀i∈I. finite (S i)" and "A ⊆ (𝒯 S I)" 
shows  "∀i∈(indices_set_formulas A). finite (S i)"
proof-
  have  "(indices_set_formulas A)⊆I" 
    using assms(1-3) indices_subset_formulas[of I S A] by auto
  thus  "∀i∈(indices_set_formulas A). finite (S i)" using assms(2) by auto
qed

lemma all_nonempty_sets1:
  assumes  "∀J⊆I. finite J ⟶  card J ≤ card (⋃ (S ` J))"
  shows "∀i∈I. (S i)≠{}" using assms by auto

lemma system_distinct_representatives_finite:
  assumes
  "∀i∈I. (S i)≠{}" and "∀i∈I. finite (S i)" and "To ⊆ (𝒯 S I)"  and "finite To" 
   and "∀J⊆(indices_set_formulas To). card J ≤ card (⋃ (S ` J))"
 shows  "∃R. system_representatives S (indices_set_formulas To) R" 
proof- 
  have 1: "finite (indices_set_formulas To)"
    using assms(4) finite_set_indices by auto
  have  "∀i∈(indices_set_formulas To). finite (S i)"
    using all_finite_sets assms(1-3) by auto
  hence  "∃R. (∀i∈(indices_set_formulas To). R i ∈ S i) ∧ 
              inj_on R (indices_set_formulas To)" 
    using 1 assms(5) marriage_HV[of "(indices_set_formulas To)" S] by auto
  then obtain R 
    where R: "(∀i∈(indices_set_formulas To). R i ∈ S i) ∧ 
              inj_on R (indices_set_formulas To)" by auto 
  thus ?thesis by(unfold system_representatives_def, auto)
qed

fun Hall_interpretation :: "('a ⇒ 'b set) ⇒ 'a set ⇒ ('a ⇒ 'b) ⇒ (('a × 'b) ⇒ v_truth)"  where
"Hall_interpretation A ℐ R = (λ(i,x).(if  i ∈ ℐ ∧ x ∈ (A i) ∧ (R i) = x  then Ttrue else Ffalse))"

lemma t_v_evaluation_index:
  assumes  "t_v_evaluation (Hall_interpretation S I R) (atom (i,x)) = Ttrue"
  shows  "(R i) = x"
proof(rule ccontr)
  assume  "(R i) ≠ x" hence "t_v_evaluation (Hall_interpretation S I R) (atom (i,x)) ≠ Ttrue" 
    by auto
  hence "t_v_evaluation (Hall_interpretation S I R) (atom (i,x)) = Ffalse" 
  using non_Ttrue[of "Hall_interpretation S I R" "atom (i,x)"] by auto 
  thus False using assms by simp
qed

lemma distinct_elements_distinct_indices:
  assumes "F = ¬.(atom (i,x) ∧. atom(i,y))" and "x≠y"  
  shows "t_v_evaluation (Hall_interpretation S I R) F = Ttrue"
proof(rule ccontr)
  assume "t_v_evaluation (Hall_interpretation S I R) F ≠ Ttrue"
  hence
  "t_v_evaluation (Hall_interpretation S I R) (¬.(atom (i,x) ∧. atom (i, y))) ≠ Ttrue" 
    using assms(1) by auto
  hence
  "t_v_evaluation (Hall_interpretation S I R) (¬.(atom (i,x) ∧. atom (i, y))) = Ffalse"
    using
  non_Ttrue[of "Hall_interpretation S I R" "¬.(atom (i,x) ∧. atom (i, y))"]
    by auto     
  hence  "t_v_evaluation (Hall_interpretation S I R) ((atom (i,x) ∧. atom (i, y))) = Ttrue" 
    using
  NegationValues1[of "Hall_interpretation S I R" "(atom (i,x) ∧. atom (i, y))"]
    by auto
  hence "t_v_evaluation (Hall_interpretation S I R) (atom (i,x)) = Ttrue" and
  "t_v_evaluation (Hall_interpretation S I R) (atom (i, y)) = Ttrue"
    using
 ConjunctionValues[of "Hall_interpretation S I R" "atom (i,x)" "atom (i, y)"]
    by auto
  hence "(R i)= x" and "(R i)= y" using t_v_evaluation_index by auto
  hence "x=y" by auto
  thus False using assms(2) by auto
qed

lemma same_element_same_index:
  assumes
  "F = ¬.(atom (i,x) ∧. atom(j,x))"  and "i∈I ∧ j∈I" and "i≠j" and "inj_on R I"
  shows "t_v_evaluation (Hall_interpretation S I R) F = Ttrue"
proof(rule ccontr)
  assume "t_v_evaluation (Hall_interpretation S I R) F ≠ Ttrue"
  hence  "t_v_evaluation (Hall_interpretation S I R) (¬.(atom (i,x) ∧. atom (j,x))) ≠ Ttrue"
    using assms(1) by auto
  hence
  "t_v_evaluation (Hall_interpretation S I R) (¬.(atom (i,x) ∧. atom (j, x))) = Ffalse" using
  non_Ttrue[of "Hall_interpretation S I R" "¬.(atom (i,x) ∧. atom (j, x))" ]
    by auto
  hence  "t_v_evaluation (Hall_interpretation S I R) ((atom (i,x) ∧. atom (j, x))) = Ttrue" 
    using 
 NegationValues1[of "Hall_interpretation S I R" "(atom (i,x) ∧. atom (j, x))"] 
    by auto
  hence "t_v_evaluation (Hall_interpretation S I R) (atom (i,x)) = Ttrue" and
  "t_v_evaluation (Hall_interpretation S I R) (atom (j, x)) = Ttrue"
    using ConjunctionValues[of "Hall_interpretation S I R" "atom (i,x)" "atom (j,x)"]
    by auto
  hence  "(R i)= x"  and  "(R j)= x" using t_v_evaluation_index by auto
  hence "(R i) = (R j)" by auto
  hence "i=j" using  `i∈I ∧ j∈I` `inj_on R I` by(unfold inj_on_def, auto)
  thus False using  `i≠j`  by auto
qed

lemma disjunctor_Ttrue_in_atomic_disjunctions:
  assumes "x ∈ set l" and "t_v_evaluation I (atom (i,x)) = Ttrue"
  shows "t_v_evaluation I (disjunction_atomic l i) = Ttrue"
proof-
  have "x ∈ set l ⟹ t_v_evaluation I (atom (i,x)) = Ttrue ⟹
  t_v_evaluation I (disjunction_atomic l i) = Ttrue" 
  proof(induct l)
    case Nil
    then show ?case by auto
  next
    case (Cons a l)
    then show  "t_v_evaluation I (disjunction_atomic (a # l) i) = Ttrue"
    proof-
      have "x = a ∨ x≠a" by auto
      thus  "t_v_evaluation I (disjunction_atomic (a # l) i) = Ttrue"
      proof(rule disjE)
        assume "x = a"
          hence
          1:"(disjunction_atomic (a#l) i) = 
             (atom (i,x)) ∨. (disjunction_atomic l i)"
          by auto 
        have "t_v_evaluation I ((atom (i,x)) ∨. (disjunction_atomic l i)) = Ttrue"  
          using Cons(3)  by(unfold t_v_evaluation_def,unfold v_disjunction_def, auto)
        thus ?thesis using 1  by auto
      next
        assume "x ≠ a"
        hence "x∈ set l" using Cons(2) by auto
        hence "t_v_evaluation I (disjunction_atomic l i ) = Ttrue"
          using Cons(1) Cons(3) by auto
        thus ?thesis
          by(unfold t_v_evaluation_def,unfold v_disjunction_def, auto)
      qed
    qed
  qed
  thus ?thesis using assms by auto
qed

lemma t_v_evaluation_disjunctions:
  assumes  "finite (S i)"
  and  "x ∈ (S i)  ∧  t_v_evaluation I (atom (i,x)) = Ttrue" 
  and  "F = disjunction_atomic (set_to_list (S i)) i " 
  shows "t_v_evaluation I F = Ttrue"
proof- 
  have "set (set_to_list (S i)) = (S i)" 
  using  set_set_to_list assms(1) by auto
  hence "x ∈ set (set_to_list (S i))"
    using assms(2) by auto
  thus "t_v_evaluation I F = Ttrue"
    using assms(2-3) disjunctor_Ttrue_in_atomic_disjunctions by auto
qed

theorem SDR_satisfiable:
  assumes "∀i∈ℐ. (A i) ≠ {}"  and  "∀i∈ℐ. finite (A i)" and  "X ⊆ (𝒯 A ℐ)"
  and  "system_representatives A ℐ R"  
shows "satisfiable X"
proof- 
  have "satisfiable (𝒯 A ℐ)"
  proof-
    have "inj_on R ℐ" using assms(4) system_representatives_def[of A ℐ R] by auto
    have "(Hall_interpretation A ℐ R) model (𝒯 A ℐ)"
    proof(unfold model_def) 
      show "∀F ∈ (𝒯 A ℐ). t_v_evaluation (Hall_interpretation A ℐ R) F = Ttrue"
      proof 
        fix F assume "F ∈ (𝒯 A ℐ)"
        show  "t_v_evaluation (Hall_interpretation A ℐ R) F  = Ttrue"
        proof-
          have "F ∈ (ℱ A ℐ) ∪ (𝒢 A ℐ) ∪ (ℋ A ℐ)" 
            using  `F ∈ (𝒯 A ℐ)` assms(3)  by(unfold 𝒯_def,auto) 
          hence  "F ∈ (ℱ A ℐ) ∨ F ∈ (𝒢 A ℐ) ∨ F ∈ (ℋ A ℐ)" by auto  
          thus ?thesis
          proof(rule disjE) 
            assume "F ∈ (ℱ A ℐ)"
            hence "∃i∈ℐ. F =  disjunction_atomic (set_to_list (A i)) i" 
              by(unfold ℱ_def,auto)
            then obtain i
              where i: "i∈ℐ" and F: "F =  disjunction_atomic (set_to_list (A i)) i"
              by auto
            have 1: "finite (A i)" using i  assms(2) by auto
            have 2: " i ∈ ℐ ∧ (R i) ∈ (A i)" 
              using i assms(4) by (unfold system_representatives_def, auto)
            hence "t_v_evaluation (Hall_interpretation A ℐ R) (atom (i,(R i))) = Ttrue"
              by auto 
            thus "t_v_evaluation (Hall_interpretation A ℐ R) F  = Ttrue"
              using 1 2 assms(4) F           
            t_v_evaluation_disjunctions
            [of A i "(R i)" "(Hall_interpretation A ℐ R)" F]
              by auto
          next
            assume "F ∈ (𝒢 A ℐ) ∨ F ∈ (ℋ A ℐ)"
            thus ?thesis
            proof(rule disjE)
              assume "F ∈ (𝒢 A ℐ)"
              hence
            "∃x.∃y.∃i. F = ¬.(atom (i,x) ∧. atom(i,y)) ∧ x∈(A i) ∧
              y∈(A i) ∧  x≠y ∧ i∈ℐ"
                by(unfold 𝒢_def, auto)
              then obtain x y i
                where F: "F = ¬.(atom (i,x) ∧. atom(i,y))" 
            and "x∈(A i) ∧ y∈(A i) ∧  x≠y ∧ i∈ℐ"
                by auto
          thus "t_v_evaluation (Hall_interpretation A ℐ R) F  = Ttrue"
            using `inj_on R ℐ` distinct_elements_distinct_indices[of F i x y A ℐ R] by auto
          next
              assume "F ∈ (ℋ A ℐ)"
              hence "∃x.∃i.∃j. F = ¬.(atom (i,x) ∧. atom(j,x)) ∧
                   x ∈ (A i) ∩ (A j) ∧ (i∈ℐ ∧ j∈ℐ ∧ i≠j)" 
                 by(unfold  ℋ_def, auto)
              then obtain x i j
              where "F = ¬.(atom (i,x) ∧. atom(j,x))"  and "(i∈ℐ ∧ j∈ℐ ∧ i≠j)" 
                 by auto
              thus "t_v_evaluation (Hall_interpretation A ℐ R) F  = Ttrue" using `inj_on R ℐ`
              same_element_same_index[of F i x j ℐ ]  by auto             
            qed
          qed
        qed
      qed
    qed
    thus "satisfiable (𝒯 A ℐ)" by(unfold satisfiable_def, auto)
  qed 
  thus "satisfiable X" using satisfiable_subset assms(3) by auto
qed 

lemma finite_is_satisfiable:
  assumes
  "∀i∈I. (S i)≠{}" and "∀i∈I. finite (S i)" and "To ⊆ (𝒯 S I)"  and  "finite To"
  and "∀J⊆(indices_set_formulas To). card J ≤ card (⋃ (S ` J))"
shows  "satisfiable To"
proof- 
  have 0: "∃R. system_representatives S (indices_set_formulas To) R" 
    using assms system_distinct_representatives_finite[of I S To] by auto
  then obtain R
    where R: "system_representatives S (indices_set_formulas To) R" by auto
  have 1: "∀i∈(indices_set_formulas To). (S i)≠{}" 
    using assms(1-3) all_nonempty_sets  by blast
  have 2: "∀i∈(indices_set_formulas To). finite (S i)" 
    using assms(1-3) all_finite_sets by blast
  have 3: "To⊆(𝒯 S (indices_set_formulas To))"
    using assms(1-3) To_subset_all_its_indices[of I S To] by auto 
  thus  "satisfiable To"
    using  1 2 3 0 SDR_satisfiable by auto
qed

lemma diag_nat:
  shows "∀y z.∃x. (y,z) = diag x" 
  using enumeration_natxnat by(unfold enumeration_def,auto)

lemma EnumFormulasHall:
  assumes "∃g. enumeration (g:: nat ⇒'a)" and "∃h. enumeration (h:: nat ⇒'b)"
  shows "∃f. enumeration (f:: nat ⇒('a ×'b )formula)"
proof-
  from assms(1) obtain g where e1: "enumeration (g:: nat ⇒'a)" by auto  
  from assms(2) obtain h where e2: "enumeration (h:: nat ⇒'b)" by auto  
  have "enumeration ((λm.(g(fst(diag m)),(h(snd(diag m))))):: nat ⇒('a ×'b))"
  proof(unfold enumeration_def) 
    show  "∀y::('a × 'b). ∃m. y = (g (fst (diag m)), h (snd (diag m)))"  
    proof
      fix y::"('a ×'b )" 
      show "∃m. y = (g (fst (diag m)), h (snd (diag m)))"
      proof-
        have  "y = ((fst y), (snd y))" by auto
        from e1 have  "∀w::'a. ∃n1. w = (g n1)" by(unfold enumeration_def, auto)
        hence "∃n1. (fst y) = (g n1)" by auto
        then obtain n1 where n1: "(fst y) = (g n1)" by auto 
        from e2 have  "∀w::'b. ∃n2. w = (h n2)" by(unfold enumeration_def, auto)
        hence "∃n2. (snd y) = (h n2)" by auto
        then obtain n2 where n2: "(snd y) = (h n2)" by auto
        have "∃m. (n1, n2) = diag m" using diag_nat by auto
        hence "∃m. (n1, n2) = (fst (diag m), snd (diag m))" by simp
        hence "∃m.((fst y), (snd y)) = (g(fst (diag m)), h(snd (diag m)))"
          using n1 n2 by blast
        thus "∃m. y = (g (fst (diag m)), h(snd (diag m)))" by auto
      qed
    qed
  qed
  thus "∃f. enumeration (f:: nat ⇒('a ×'b )formula)" 
    using EnumerationFormulasP1 by auto 
qed

theorem all_formulas_satisfiable:
 fixes S :: "('a::countable ⇒ 'b::countable set)" and I :: "'a set"
 assumes "∀i∈(I::'a set). finite (S i)" and "∀J⊆I. finite J ⟶  card J ≤ card (⋃ (S ` J))"
shows "satisfiable (𝒯 S I)"
proof-
  have "∀ A. A ⊆ (𝒯 S I) ∧ (finite A) ⟶ satisfiable A"
  proof(rule allI, rule impI) 
    fix A assume "A ⊆ (𝒯 S I) ∧ (finite A)"
    hence hip1:  "A ⊆ (𝒯 S I)" and  hip2: "finite A" by auto
    show "satisfiable A"
    proof -
      have 0: "∀i∈I. (S i)≠{}" using assms(2) all_nonempty_sets1 by auto
      hence 1: "(indices_set_formulas A)⊆I"  
        using assms(1) hip1 indices_subset_formulas[of I S A] by auto
      have 2: "finite (indices_set_formulas A)" 
        using hip2 finite_set_indices by auto
      have 3: "card (indices_set_formulas A) ≤ card(⋃ (S `(indices_set_formulas A)))"
        using 1 2 assms(2) by auto
      have "∀J⊆(indices_set_formulas A). card J ≤ card(⋃ (S ` J))"
     proof(rule allI)
       fix J
       show "J ⊆ indices_set_formulas A ⟶ card J ≤ card (⋃ (S ` J)) "
       proof(rule impI)
         assume hip: "J⊆(indices_set_formulas A)"              
       hence 4: "finite J" 
         using 2  rev_finite_subset by auto 
       have "J⊆I" using hip 1 by auto
       thus "card J ≤ card (⋃ (S ` J))" using 4  assms(2) by auto      
     qed
   qed
   thus "satisfiable A"
     using 0 assms(1) hip1 hip2 finite_is_satisfiable[of I S A]  by auto
 qed
qed
  thus "satisfiable (𝒯 S I)" using 
  Compacteness_Theorem[of "(𝒯 S I)"]
    by auto
qed

fun SDR ::  "(('a × 'b) ⇒ v_truth) ⇒ ('a ⇒ 'b set) ⇒ 'a set ⇒ ('a ⇒'b )"
  where
"SDR M S I = (λi. (THE x. (t_v_evaluation M (atom (i,x)) = Ttrue) ∧ x∈(S i)))"

lemma existence_representants:
 assumes "i ∈ I" and "M model (ℱ S I)" and "finite(S i)"  
  shows "∃x. (t_v_evaluation M (atom (i,x)) = Ttrue) ∧  x ∈ (S i)" 
proof- 
  from  `i ∈ I`  
  have  "(disjunction_atomic (set_to_list (S i)) i) ∈ (ℱ S I)" 
    by(unfold ℱ_def,auto)
  hence "t_v_evaluation M (disjunction_atomic(set_to_list (S i)) i) = Ttrue"
    using assms(2) model_def[of M "ℱ S I"] by auto 
  hence 1: "∃x. x ∈ set (set_to_list (S i)) ∧ (t_v_evaluation M (atom (i,x)) = Ttrue)"
    using t_v_evaluation_atom[of M "(set_to_list (S i))" i] by auto
  thus  "∃x. (t_v_evaluation M (atom (i,x)) = Ttrue) ∧  x ∈ (S i)" 
    using   `finite(S i)` set_set_to_list[of "(S i)"] by auto
qed

lemma unicity_representants:
  shows  "∀y.(x∈(S i) ∧ y∈(S i) ∧  x≠y ∧ i∈I) ⟶
          (¬.(atom (i,x) ∧. atom(i,y))∈ (𝒢 S I))"
proof(rule allI) 
  fix y
  show "x∈(S i) ∧ y∈(S i) ∧  x≠y ∧ i∈I ⟶ 
       (¬.(atom (i,x) ∧. atom(i,y))∈ (𝒢 S I))"
  proof(rule impI)
    assume "x∈(S i) ∧ y∈(S i) ∧  x≠y ∧ i∈I"
    thus  "¬.(atom (i,x) ∧. atom(i,y)) ∈ (𝒢 S I)"
   by(unfold 𝒢_def, auto)
  qed
qed

lemma unicity_selection_representants:
 assumes "i ∈ I" and "M model (𝒢 S I)" 
  shows  "∀y.(x∈(S i) ∧ y∈(S i) ∧  x≠y ∧ i∈I) ⟶ 
  (t_v_evaluation M (¬.(atom (i,x) ∧. atom(i,y))) = Ttrue)"
proof-
  have   "∀y.(x∈(S i) ∧ y∈(S i) ∧  x≠y ∧ i∈I) ⟶ 
  (¬.(atom (i,x) ∧. atom(i,y))∈ (𝒢 S I))"
    using unicity_representants[of x S i] by auto
  thus  "∀y.(x∈(S i) ∧ y∈(S i) ∧  x≠y ∧ i∈I) ⟶ 
  (t_v_evaluation M (¬.(atom (i,x) ∧. atom(i,y))) = Ttrue)"
    using assms(2)  model_def[of M "𝒢 S I"] by blast
qed

lemma uniqueness_satisfaction:
  assumes "t_v_evaluation M (atom (i,x)) = Ttrue ∧ x∈(S i)" and
  "∀y. y ∈ (S i) ∧ x≠y  ⟶  t_v_evaluation M (atom (i, y)) = Ffalse"  
shows "∀z. t_v_evaluation M (atom (i, z)) = Ttrue ∧ z∈(S i) ⟶ z = x"
proof(rule allI)
  fix z 
  show "t_v_evaluation M (atom (i, z)) = Ttrue ∧ z ∈ S i  ⟶ z = x" 
  proof(rule impI)
    assume hip: "t_v_evaluation M (atom (i, z)) = Ttrue ∧ z ∈ (S i)"  
    show "z = x"
    proof(rule ccontr)
      assume 1: "z ≠ x"
      have   2: "z ∈ (S i)" using hip by auto
      hence  "t_v_evaluation M (atom(i,z)) =  Ffalse" using 1 assms(2) by auto
      thus False using hip by auto
    qed
  qed
qed

lemma uniqueness_satisfaction_in_Si:
  assumes "t_v_evaluation M (atom (i,x)) = Ttrue ∧ x∈(S i)" and
  "∀y. y ∈ (S i) ∧ x≠y ⟶ (t_v_evaluation M (¬.(atom (i,x) ∧. atom(i,y))) = Ttrue)"
  shows "∀y. y ∈ (S i)  ∧ x≠y  ⟶  t_v_evaluation M (atom (i, y)) = Ffalse"
proof(rule allI, rule impI)
  fix y
  assume hip: "y ∈ S i ∧ x ≠ y"
  show "t_v_evaluation M (atom (i, y)) = Ffalse"
  proof(rule ccontr)
    assume "t_v_evaluation M (atom (i, y)) ≠ Ffalse" 
    hence "t_v_evaluation M (atom (i, y)) = Ttrue" using  Bivaluation by blast
    hence 1: "t_v_evaluation M (atom (i,x) ∧. atom(i,y))  = Ttrue"
      using assms(1) v_conjunction_def by auto
    have "t_v_evaluation M (¬.(atom (i,x) ∧. atom(i,y))) = Ttrue"
      using hip assms(2) by auto
    hence "t_v_evaluation M (atom (i,x) ∧. atom(i,y)) = Ffalse" 
      using NegationValues2  by blast
    thus False using 1  by auto
  qed      
qed

lemma uniqueness_aux1:
  assumes  "t_v_evaluation M (atom (i,x)) = Ttrue ∧ x∈(S i)"
  and  "∀y. y ∈ (S i) ∧ x≠y ⟶ (t_v_evaluation M (¬.(atom (i,x) ∧. atom(i,y))) = Ttrue)"
shows "∀z. t_v_evaluation M (atom (i, z)) = Ttrue ∧ z∈(S i) ⟶ z = x" 
  using assms uniqueness_satisfaction_in_Si[of M i x ]  uniqueness_satisfaction[of M i x] by blast 

lemma uniqueness_aux2:
  assumes "t_v_evaluation M (atom (i,x)) = Ttrue ∧ x∈(S i)" and
  "(⋀z.(t_v_evaluation M (atom (i, z)) = Ttrue ∧ z∈(S i))  ⟹ z = x)"
shows "(THE a. (t_v_evaluation M (atom (i,a)) = Ttrue) ∧ a∈(S i)) = x" 
  using assms by(rule the_equality)

lemma uniqueness_aux:
  assumes  "t_v_evaluation M (atom (i,x)) = Ttrue ∧ x∈(S i)" and
  "∀y. y ∈ (S i) ∧ x≠y ⟶ (t_v_evaluation M (¬.(atom (i,x) ∧. atom(i,y))) = Ttrue)"
shows  "(THE a. (t_v_evaluation M (atom (i,a)) = Ttrue) ∧ a∈(S i)) = x" 
  using assms  uniqueness_aux1[of M i x ] uniqueness_aux2[of M i x] by blast

lemma function_SDR:
  assumes "i ∈ I" and "M model (ℱ S I)" and "M model (𝒢 S I)" and "finite(S i)"
shows "∃!x. (t_v_evaluation M (atom (i,x)) = Ttrue) ∧  x ∈ (S i) ∧ (SDR  M S I i) = x" 
proof- 
  have  "∃x. (t_v_evaluation M (atom (i,x)) = Ttrue) ∧  x ∈ (S i)" 
    using assms(1-2,4) existence_representants by auto 
  then obtain x where x: "(t_v_evaluation M (atom (i,x)) = Ttrue) ∧  x ∈ (S i)"
    by auto
  moreover
  have "∀y.(x∈(S i) ∧ y∈(S i) ∧  x≠y ∧ i∈I) ⟶ 
  (t_v_evaluation M (¬.(atom (i,x) ∧. atom(i,y))) = Ttrue)" 
    using assms(1,3) unicity_selection_representants[of i I M S]  by auto
  hence "(THE a. (t_v_evaluation M (atom (i,a)) = Ttrue) ∧ a∈(S i)) = x"
   using x  `i ∈ I`  uniqueness_aux[of M i x] by auto 
  hence "SDR M S I i = x"  by auto
  hence "(t_v_evaluation M (atom (i,x)) = Ttrue ∧ x ∈ (S i)) ∧  SDR M S I i = x"
    using x by auto
  thus ?thesis  by auto
qed

lemma aux_for_ℋ_formulas:
  assumes
  "(t_v_evaluation M (atom (i,a)) = Ttrue) ∧ a ∈ (S i)"
  and "(t_v_evaluation M (atom (j,b)) = Ttrue) ∧ b ∈ (S j)" 
  and  "i∈I ∧ j∈I ∧ i≠j" 
  and "(a ∈ (S i) ∩ (S j) ∧ i∈I ∧ j∈I ∧ i≠j ⟶
  (t_v_evaluation M (¬.(atom (i,a) ∧. atom(j,a))) = Ttrue))"
  shows  "a ≠ b"
proof(rule ccontr)
  assume  "¬ a ≠ b" 
  hence hip: "a=b" by auto
  hence "t_v_evaluation M (atom (i, a)) = Ttrue" and  "t_v_evaluation M (atom (j, a)) = Ttrue"
    using assms by auto
  hence "t_v_evaluation M (atom (i, a) ∧. atom(j,a)) = Ttrue" using v_conjunction_def
    by auto
  hence "t_v_evaluation M (¬.(atom (i, a) ∧. atom(j,a))) = Ffalse" 
    using v_negation_def by auto
  moreover
  have  "a ∈ (S i) ∩ (S j)" using hip assms(1-2) by auto
  hence "t_v_evaluation M (¬.(atom (i, a) ∧. atom(j, a))) = Ttrue" 
    using assms(3-4) by auto
  ultimately show False by auto
qed

lemma model_of_all:
  assumes  "M model (𝒯 S I)"
  shows  "M model (ℱ S I)" and  "M model (𝒢 S I)" and  "M model (ℋ S I)" 
proof(unfold model_def)
  show "∀F∈ℱ S I. t_v_evaluation M F = Ttrue"
  proof
    fix F
    assume "F∈ (ℱ S I)" hence "F∈(𝒯 S I)" by(unfold 𝒯_def, auto) 
    thus "t_v_evaluation M F = Ttrue" using assms by(unfold model_def, auto)
  qed
next
  show "∀F∈(𝒢 S I). t_v_evaluation M F = Ttrue"
  proof
    fix F
    assume "F∈(𝒢 S I)" hence "F∈(𝒯 S I)" by(unfold 𝒯_def, auto) 
    thus "t_v_evaluation M F = Ttrue" using assms by(unfold model_def, auto)
  qed
next
  show "∀F∈(ℋ S I). t_v_evaluation M F = Ttrue"
  proof
    fix F
    assume "F∈(ℋ S I)" hence "F∈(𝒯 S I)" by(unfold 𝒯_def, auto) 
    thus "t_v_evaluation M F = Ttrue" using assms by(unfold model_def, auto)
  qed
qed

lemma sets_have_distinct_representants:
  assumes
  hip1: "i∈I" and  hip2: "j∈I" and  hip3: "i≠j" and  hip4: "M model (𝒯 S I)"
  and hip5: "finite(S i)" and  hip6: "finite(S j)"
  shows " SDR M S I i  ≠  SDR M S I j" 
proof-
  have 1: "M model ℱ S I" and 2:  "M model 𝒢 S I"
    using hip4 model_of_all by auto
  hence "∃!x. (t_v_evaluation M (atom (i,x)) = Ttrue) ∧ x ∈ (S i) ∧  SDR M S I i = x"
    using  hip1  hip4  hip5 function_SDR[of i I M S] by auto  
  then obtain x where
  x1: "(t_v_evaluation M (atom (i,x)) = Ttrue) ∧ x ∈ (S i)" and x2: "SDR M S I i = x"
    by auto 
  have "∃!y. (t_v_evaluation M (atom (j,y)) = Ttrue) ∧ y ∈ (S j) ∧ SDR M S I j = y"
  using 1 2  hip2  hip4  hip6 function_SDR[of j I M S] by auto   
  then obtain y where
  y1: "(t_v_evaluation M (atom (j,y)) = Ttrue) ∧ y ∈ (S j)" and y2: "SDR M S I j = y"
    by auto
  have "(x ∈ (S i) ∩ (S j) ∧ i∈I ∧ j∈I ∧ i≠j) ⟶
  (¬.(atom (i,x) ∧. atom(j,x))∈ (ℋ S I))"
    by(unfold  ℋ_def, auto)
  hence "(x ∈ (S i) ∩ (S j) ∧ i∈I ∧ j∈I ∧ i≠j) ⟶
  (¬.(atom (i,x) ∧. atom(j,x)) ∈ (𝒯 S I))"
    by(unfold  𝒯_def, auto)
  hence "(x ∈ (S i) ∩ (S j) ∧ i∈I ∧ j∈I ∧ i≠j) ⟶
  (t_v_evaluation M (¬.(atom (i,x) ∧. atom(j,x))) = Ttrue)" 
    using hip4 model_def[of M "𝒯 S I"] by auto
  hence "x ≠ y" using x1 y1 assms(1-3) aux_for_ℋ_formulas[of M i x  S  j y I] 
    by auto
  thus ?thesis using x2 y2 by auto
qed  

lemma satisfiable_representant:
  assumes "satisfiable (𝒯 S I)" and "∀i∈I. finite (S i)"
  shows "∃R. system_representatives S I R"
proof-
  from assms have "∃M. M model (𝒯 S I)"  by(unfold satisfiable_def)
  then obtain M where M: "M model (𝒯 S I)" by auto 
  hence  "system_representatives S I (SDR M S I)" 
  proof(unfold system_representatives_def) 
    show "(∀i∈I. (SDR M S I i) ∈ (S i)) ∧ inj_on (SDR M S I) I" 
    proof(rule conjI)
      show "∀i∈I. (SDR M S I i) ∈ (S i)"
      proof 
        fix i
        assume i: "i ∈ I"
        have "M model ℱ S I" and 2: "M model 𝒢 S I" using M model_of_all
          by auto
        thus "(SDR M S I i) ∈ (S i)"
          using i M assms(2) model_of_all[of M S I]
                  function_SDR[of i I M S ] by auto 
      qed
    next
      show "inj_on (SDR M S I) I"
      proof(unfold  inj_on_def)
        show "∀i∈I. ∀j∈I. SDR M S I i = SDR M S I j ⟶ i = j"
        proof 
          fix i 
          assume 1:  "i ∈ I"
          show "∀j∈I. SDR M S I i = SDR M S I j ⟶ i = j"
          proof 
            fix j
            assume 2:  "j ∈ I"
            show "SDR M S I i = SDR M S I j ⟶ i = j"
            proof(rule ccontr)
              assume  "¬ (SDR M S I i = SDR M S I j ⟶ i = j)"
              hence 5:  "SDR M S I i = SDR M S I j" and 6:  "i≠ j" by auto
              have  3: "finite(S i)" and 4: "finite(S j)" using 1 2  assms(2) by auto
              have "SDR M S I i ≠ SDR M S I j"
                using 1 2 3 4 6 M sets_have_distinct_representants[of i I j M S] by auto
              thus False  using 5 by auto
            qed
          qed 
        qed
      qed
    qed
  qed
  thus  "∃R. system_representatives S I R" by auto
qed

theorem Hall:
  fixes S :: "('a::countable ⇒ 'b::countable set)" and I :: "'a set"
  assumes Finite: "∀i∈I. finite (S i)"
  and Marriage: "∀J⊆I. finite J ⟶  card J ≤ card (⋃ (S ` J))"
 shows "∃R. system_representatives S I R"
proof-  
  have "satisfiable (𝒯 S I)" using assms all_formulas_satisfiable[of I] by auto
  thus ?thesis using Finite Marriage satisfiable_representant[of S I] by auto
qed

theorem marriage_necessity:
  fixes A :: "'a ⇒ 'b set" and I :: "'a set"
  assumes "∀ i∈I. finite (A i)"
  and "∃R. (∀i∈I. R i ∈ A i) ∧ inj_on R I" (is "∃R. ?R R A & ?inj R A")
  shows "∀J⊆I. finite J ⟶ card J ≤ card (⋃(A ` J))"
proof clarify
  fix J
  assume "J ⊆ I" and 1: "finite J"
  show "card J ≤ card (⋃(A ` J))"
  proof-
    from assms(2) obtain R where "?R R A" and "?inj R A" by auto
    have "inj_on R J" by(rule subset_inj_on[OF ‹?inj R A› ‹J⊆I›])
    moreover have "(R ` J) ⊆ (⋃(A ` J))" using ‹J⊆I› ‹?R R A› by auto
    moreover have "finite (⋃(A ` J))" using ‹J⊆I› 1 assms
      by auto
    ultimately show ?thesis by (rule card_inj_on_le)
  qed
qed

end

