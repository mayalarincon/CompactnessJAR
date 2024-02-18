(* Formalization taken from: 
   Fabián Fernando Serrano Suárez. Formalización en Isar de la
   Meta-Lógica de Primer Orden. PhD thesis, 
   Departamento de Ciencias de la Computación e Inteligencia Artificial,
   Universidadde Sevilla, Spain, 2012.
   https://idus.us.es/handle/11441/57780.  In Spanish  *)

theory Compactness

imports Main 
"HOL-Library.Countable_Set"
"ModelExistence/ModelExistence"

begin

lemma UnsatisfiableAtom:
  shows "¬(satisfiable {F, ¬.F})"
proof (rule notI)
  assume hip: "satisfiable {F, ¬.F}" 
  show "False"
  proof -
    have  "∃I. I model {F, ¬.F}" using hip by(unfold satisfiable_def, auto) 
    then obtain I where I: "(t_v_evaluation I F) = Ttrue" 
      and "(t_v_evaluation I (¬.F)) = Ttrue"  
      by(unfold model_def, auto)
    thus "False" by(auto simp add: v_negation_def)
  qed
qed
 

lemma consistenceP_Prop1:
  assumes "∀ (A::'b formula set). (A⊆ W ∧ finite A) ⟶ satisfiable A"
  shows "(∀P. ¬ (Atom P ∈ W ∧ (¬. Atom P) ∈ W))"
proof (rule allI notI)+
  fix P
  assume h1: "Atom P ∈ W ∧ (¬.Atom P) ∈ W"
  show "False"
  proof - 
    have "{Atom P, (¬.Atom P)} ⊆ W" using h1 by simp 
    moreover
    have "finite {Atom P, (¬.Atom P)}" by simp  
    ultimately
    have "{Atom P, (¬.Atom P)} ⊆ W ∧ finite {Atom P, (¬.Atom P)}" by simp  
    moreover
    have "({Atom P, (¬.Atom P)}⊆ W ∧ finite {Atom P, (¬.Atom P)}) ⟶
          satisfiable {Atom P, (¬.Atom P)}" 
      using assms by(rule_tac x = "{Atom P, (¬.Atom P)}" in allE, auto)
    ultimately
    have "satisfiable {Atom P, (¬.Atom P)}" by simp
    thus "False" using UnsatisfiableAtom by auto
  qed
qed

lemma UnsatisfiableFF:
  shows "¬ (satisfiable {FF})"
proof -
  have "∀ I. t_v_evaluation I FF = Ffalse" by simp
  hence "∀ I. ¬ (I model {FF})"  by(unfold model_def, auto) 
  thus ?thesis by(unfold satisfiable_def, auto)
qed

lemma consistenceP_Prop2:
  assumes "∀ (A::'b formula set). (A⊆ W ∧ finite A) ⟶ satisfiable A"
  shows "FF ∉ W"
proof (rule notI)
  assume hip: "FF ∈ W"
  show "False"
  proof -
    have "{FF} ⊆ W" using hip by simp 
    moreover
    have "finite {FF}" by simp  
    ultimately
    have "{FF} ⊆ W ∧ finite {FF}" by simp  
    moreover
    have "({FF::'b formula} ⊆ W ∧ finite {FF}) ⟶ 
          satisfiable {FF::'b formula}" 
      using assms by(rule_tac x = "{FF::'b formula}" in allE, auto)
    ultimately
    have "satisfiable {FF::'b formula}" by simp
    thus "False" using UnsatisfiableFF by auto
  qed
qed

lemma UnsatisfiableFFa:
  shows "¬ (satisfiable {¬.TT})"
proof -
  have "∀ I. t_v_evaluation I TT = Ttrue" by simp  
  have "∀ I. t_v_evaluation I (¬.TT) = Ffalse" by(auto simp add:v_negation_def)
  hence "∀ I. ¬ (I model {¬.TT})"  by(unfold model_def, auto) 
  thus ?thesis by(unfold satisfiable_def, auto)
qed

lemma consistenceP_Prop3:
  assumes "∀ (A::'b formula set). (A⊆ W ∧ finite A) ⟶ satisfiable A"
  shows "¬.TT ∉ W"
proof (rule notI)
  assume hip: "¬.TT ∈ W"
  show "False"
  proof -
    have "{¬.TT} ⊆ W" using hip by simp 
    moreover
    have "finite {¬.TT}" by simp  
    ultimately
    have "{¬.TT} ⊆ W ∧ finite {¬.TT}" by simp  
    moreover
    have "({¬.TT::'b formula} ⊆ W ∧ finite {¬.TT}) ⟶ 
          satisfiable {¬.TT::'b formula}" 
      using assms by(rule_tac x = "{¬.TT::'b formula}" in allE, auto)
    ultimately
    have "satisfiable {¬.TT::'b formula}" by simp
    thus "False" using UnsatisfiableFFa by auto
  qed
qed

lemma Subset_Sat:
  assumes hip1: "satisfiable S" and hip2: "S'⊆ S"
  shows "satisfiable S'"
proof -
  have "∃I. ∀ F ∈ S. t_v_evaluation I F = Ttrue" using hip1 
    by (unfold satisfiable_def, unfold model_def, auto)
  hence "∃I. ∀ F ∈ S'. t_v_evaluation I F = Ttrue" using hip2 by auto
  thus ?thesis by(unfold satisfiable_def, unfold model_def, auto)
qed
text‹ ›
lemma satisfiableUnion1:
  assumes "satisfiable (A ∪ {¬.¬.F})" 
  shows "satisfiable (A ∪ {F})"
proof -
  have "∃I. ∀ G ∈ (A ∪ {¬.¬.F}). t_v_evaluation I G = Ttrue"  
    using assms by(unfold satisfiable_def, unfold model_def, auto)
  then obtain I where I: "∀ G ∈ (A ∪ {¬.¬.F}). t_v_evaluation I G = Ttrue" 
    by auto      
  hence 1: "∀ G ∈ A. t_v_evaluation I G = Ttrue" 
    and 2: "t_v_evaluation I (¬.¬.F) = Ttrue" 
    by auto
  have "typeFormula (¬.¬.F) = NoNo" by auto
  hence "t_v_evaluation I  F = Ttrue" using EquivNoNoComp[of "¬.¬.F"] 2 
    by (unfold equivalent_def, unfold Comp1_def, auto)          
  hence "∀ G ∈ A ∪ {F}. t_v_evaluation I G = Ttrue" using 1 by auto  
  thus "satisfiable (A ∪ {F})" 
    by(unfold satisfiable_def, unfold model_def, auto)
qed


lemma consistenceP_Prop4:
  assumes hip1: "∀ (A::'b formula set). (A⊆ W ∧ finite A) ⟶ satisfiable A" 
  and hip2: "¬.¬.F ∈ W"
  shows "∀ (A::'b formula set). (A⊆ W ∪ {F} ∧ finite A) ⟶ satisfiable A"
proof (rule allI, rule impI)+
  fix A
  assume hip: "A ⊆ W ∪ {F} ∧ finite A"
  show "satisfiable A"
  proof -
    have "A-{F} ⊆ W ∧ finite (A-{F})" using hip by auto
    hence "(A-{F}) ∪ {¬.¬.F} ⊆ W ∧ finite ((A-{F}) ∪ {¬.¬.F})" 
      using hip2 by auto  
    hence "satisfiable ((A-{F}) ∪ {¬.¬.F})" using hip1 by auto
    hence "satisfiable ((A-{F}) ∪ {F})" using  satisfiableUnion1 by blast
    moreover
    have "A⊆ (A-{F}) ∪ {F}" by auto
    ultimately
    show "satisfiable A" using Subset_Sat by auto
  qed
qed


lemma satisfiableUnion2:
  assumes hip1: "FormulaAlfa F" and hip2: "satisfiable (A ∪ {F})" 
  shows "satisfiable (A ∪ {Comp1 F,Comp2 F})"
proof -   
  have "∃I.∀ G ∈ A ∪ {F}. t_v_evaluation I G = Ttrue"  
    using hip2 by(unfold satisfiable_def, unfold model_def, auto)
  then obtain I where I:  "∀ G ∈ A ∪ {F}. t_v_evaluation I G = Ttrue" by auto      
  hence 1: "∀ G ∈ A. t_v_evaluation I G = Ttrue" and 2: "t_v_evaluation I F = Ttrue" by auto
  have "typeFormula F = Alfa" using hip1 noAlfaBeta noAlfaNoNo by auto
  hence "equivalent F (Comp1 F ∧. Comp2 F)" 
    using 2 EquivAlfaComp[of F] by auto  
  hence  "t_v_evaluation I (Comp1 F ∧. Comp2 F) = Ttrue" 
    using 2 by( unfold equivalent_def, auto) 
  hence "t_v_evaluation I (Comp1 F) = Ttrue ∧ t_v_evaluation I (Comp2 F) = Ttrue"  
    using ConjunctionValues by auto 
  hence "∀ G ∈ A ∪ {Comp1 F, Comp2 F} . t_v_evaluation I G = Ttrue" using 1 by auto
  thus "satisfiable (A ∪ {Comp1 F,Comp2 F})" 
    by (unfold satisfiable_def, unfold model_def, auto)
qed

lemma consistenceP_Prop5:
  assumes hip0: "FormulaAlfa F" 
  and hip1: "∀ (A::'b formula set). (A⊆ W ∧ finite A) ⟶ satisfiable A" 
  and hip2: "F ∈ W"
  shows "∀ (A::'b formula set). (A⊆ W ∪ {Comp1 F, Comp2 F} ∧ finite A) ⟶ 
  satisfiable A"
proof (rule allI, rule impI)+
  fix A
  assume hip: "A ⊆ W ∪ {Comp1 F, Comp2 F} ∧ finite A"
  show "satisfiable A"
  proof -
    have "A-{Comp1 F, Comp2 F} ⊆ W ∧ finite (A-{Comp1 F, Comp2 F})" 
      using hip by auto
    hence "(A-{Comp1 F, Comp2 F}) ∪ {F} ⊆ W ∧ 
           finite ((A-{Comp1 F, Comp2 F}) ∪ {F})" 
      using hip2 by auto  
    hence "satisfiable ((A-{Comp1 F, Comp2 F}) ∪ {F})" 
      using hip1 by auto
    hence "satisfiable ((A-{Comp1 F, Comp2 F}) ∪ {Comp1 F, Comp2 F})"
      using hip0 satisfiableUnion2 by auto
    moreover
    have  "A ⊆ (A-{Comp1 F, Comp2 F}) ∪ {Comp1 F, Comp2 F}" by auto
    ultimately
    show "satisfiable A" using Subset_Sat by auto
  qed
qed


lemma satisfiableUnion3:
  assumes hip1: "FormulaBeta F" and hip2: "satisfiable (A ∪ {F})" 
  shows "satisfiable (A ∪ {Comp1 F}) ∨ satisfiable (A ∪ {Comp2 F})" 
proof - 
  obtain I where I: "∀G ∈ (A ∪ {F}). t_v_evaluation I G = Ttrue"
  using hip2 by(unfold satisfiable_def, unfold model_def, auto) 
  hence S1: "∀G ∈ A. t_v_evaluation I G = Ttrue" 
    and S2: " t_v_evaluation I F = Ttrue" 
    by auto
  have V: "t_v_evaluation I (Comp1 F) = Ttrue ∨ t_v_evaluation I (Comp2 F) = Ttrue" 
    using hip1 S2 EquivBetaComp[of F] DisjunctionValues
    by (unfold equivalent_def, auto)       
  have "((∀G ∈ A. t_v_evaluation I G = Ttrue) ∧ t_v_evaluation I (Comp1 F) = Ttrue) ∨
        ((∀G ∈ A. t_v_evaluation I G = Ttrue) ∧ t_v_evaluation I (Comp2 F) = Ttrue)" 
    using V
  proof (rule disjE)
    assume "t_v_evaluation I (Comp1 F) = Ttrue" 
    hence "(∀G ∈ A. t_v_evaluation I G = Ttrue) ∧ t_v_evaluation I (Comp1 F) = Ttrue"
      using S1 by auto
    thus ?thesis by simp  
  next
    assume "t_v_evaluation I (Comp2 F) = Ttrue"
    hence "(∀G ∈ A. t_v_evaluation I G = Ttrue) ∧ t_v_evaluation I (Comp2 F) = Ttrue"
      using S1 by auto
    thus ?thesis by simp
  qed
  hence "(∀G ∈ A ∪ {Comp1 F}. t_v_evaluation I G = Ttrue) ∨ 
         (∀G ∈ A ∪ {Comp2 F}. t_v_evaluation I G = Ttrue)" 
    by auto 
  hence "(∃I.∀G ∈ A ∪ {Comp1 F}. t_v_evaluation I G = Ttrue) ∨
         (∃I.∀G ∈ A ∪ {Comp2 F}. t_v_evaluation I G = Ttrue)" 
    by auto
  thus "satisfiable (A ∪ {Comp1 F}) ∨ satisfiable (A ∪ {Comp2 F})"
  by (unfold satisfiable_def, unfold model_def, auto)
qed


lemma consistenceP_Prop6:
  assumes hip0: "FormulaBeta F" 
  and hip1: "∀ (A::'b formula set). (A⊆ W ∧ finite A) ⟶ satisfiable A" 
  and hip2: "F ∈ W"
  shows "(∀ (A::'b formula set). (A⊆ W ∪ {Comp1 F} ∧ finite A) ⟶ 
  satisfiable A) ∨
  (∀ (A::'b formula set). (A⊆ W ∪ {Comp2 F} ∧ finite A) ⟶ 
  satisfiable A)"
proof -
  { assume hip3:"¬((∀ (A::'b formula set). (A⊆ W ∪ {Comp1 F} ∧ finite A) ⟶ 
    satisfiable A) ∨
    (∀ (A::'b formula set). (A⊆ W ∪ {Comp2 F} ∧ finite A) ⟶ 
    satisfiable A))" 
    have "False"
    proof - 
      obtain A B where A1: "A ⊆ W ∪ {Comp1 F}" 
        and A2: "finite A" 
        and A3:" ¬ satisfiable A" 
        and B1: "B ⊆ W ∪ {Comp2 F}" 
        and B2: "finite B" 
        and B3: "¬ satisfiable B" 
        using hip3 by auto     
      have a1: "A - {Comp1 F} ⊆ W" 
        and a2: "finite (A - {Comp1 F})" 
        using A1 and A2 by auto
      hence "satisfiable (A - {Comp1 F})" using hip1 by simp  
      have b1: "B - {Comp2 F} ⊆ W" 
        and b2: "finite (B - {Comp2 F})" 
        using B1 and B2 by auto
      hence "satisfiable (B - {Comp2 F})" using hip1 by simp
      moreover
      have "(A - {Comp1 F}) ∪ (B - {Comp2 F}) ∪ {F} ⊆ W" 
        and "finite ((A - {Comp1 F}) ∪ (B - {Comp2 F}) ∪ {F})"
        using a1 a2 b1 b2 hip2 by auto
      hence "satisfiable ((A - {Comp1 F}) ∪ (B - {Comp2 F}) ∪ {F})" 
        using hip1 by simp
      hence "satisfiable ((A - {Comp1 F}) ∪ (B - {Comp2 F}) ∪ {Comp1 F})
      ∨ satisfiable ((A - {Comp1 F}) ∪ (B - {Comp2 F}) ∪ {Comp2 F})"
        using hip0 satisfiableUnion3 by auto  
      moreover
      have "A ⊆ (A - {Comp1 F}) ∪ (B - {Comp2 F}) ∪ {Comp1 F}" 
        and "B ⊆ (A - {Comp1 F}) ∪ (B - {Comp2 F}) ∪ {Comp2 F}" 
        by auto
      ultimately
      have "satisfiable A ∨ satisfiable B" using Subset_Sat by auto
      thus "False" using A3 B3 by simp
    qed } 
  thus ?thesis by auto
qed

lemma ConsistenceCompactness:   
  shows "consistenceP{W::'b formula set. ∀A. (A⊆ W ∧ finite A) ⟶ 
  satisfiable A}"
proof (unfold consistenceP_def, rule allI, rule impI)  
  let ?C = "{W::'b formula set.  ∀A. (A⊆ W ∧ finite A) ⟶ satisfiable A}"
  fix W ::" 'b formula set"  
  assume "W ∈ ?C"  
  hence  hip: "∀A. (A⊆ W ∧ finite A) ⟶ satisfiable A" by simp
  show "(∀P. ¬ (atom P ∈ W ∧ (¬.atom P ) ∈ W)) ∧
        FF ∉ W ∧
        ¬.TT ∉ W ∧
        (∀F. ¬.¬.F ∈ W ⟶ W ∪ {F} ∈ ?C) ∧
        (∀F. (FormulaAlfa F) ∧ F ∈ W ⟶ 
        (W ∪  {Comp1 F, Comp2 F} ∈ ?C)) ∧
        (∀F. (FormulaBeta F) ∧ F ∈ W ⟶ 
        (W ∪ {Comp1 F} ∈ ?C ∨ W ∪ {Comp2 F} ∈ ?C))"
  proof -   
    have "(∀P. ¬ (atom P ∈ W ∧ (¬. atom P) ∈ W))" 
      using hip  consistenceP_Prop1 by simp
    moreover
    have "FF ∉ W" using hip consistenceP_Prop2 by auto
    moreover 
    have "¬. TT ∉ W" using hip consistenceP_Prop3 by auto
    moreover
    have "∀F. (¬.¬.F) ∈ W ⟶ W ∪ {F} ∈ ?C"
    proof (rule allI impI)+
      fix F
      assume hip1: "¬.¬.F ∈ W"    
      show "W ∪ {F} ∈ ?C" using hip hip1 consistenceP_Prop4 by simp
    qed
    moreover
    have
    "∀F. (FormulaAlfa F) ∧ F ∈ W ⟶ (W ∪  {Comp1 F, Comp2 F} ∈ ?C)" 
    proof (rule allI impI)+
      fix F 
      assume "FormulaAlfa F ∧ F ∈ W"      
      thus "W ∪ {Comp1 F, Comp2 F} ∈ ?C" using hip consistenceP_Prop5[of F] by blast
    qed
    moreover         
    have "∀F. (FormulaBeta F) ∧ F ∈ W ⟶ 
              (W ∪ {Comp1 F} ∈ ?C ∨ W ∪ {Comp2 F} ∈ ?C)"
    proof (rule allI impI)+
      fix F 
      assume "(FormulaBeta F) ∧ F ∈ W" 
      thus "W ∪ {Comp1 F} ∈ ?C ∨ W ∪ {Comp2 F} ∈ ?C" 
        using hip consistenceP_Prop6[of F] by blast      
    qed 
    ultimately 
    show ?thesis by auto
  qed
qed

lemma countable_enumeration_formula:
  shows  "∃f. enumeration (f:: nat ⇒'a::countable formula)" 
  by (metis(full_types) EnumerationFormulasP1
       enumeration_def surj_def surj_from_nat)  

theorem Compacteness_Theorem:
  assumes "∀A. (A ⊆ (S:: 'a::countable formula set) ∧ finite A) ⟶ satisfiable A" 
  shows "satisfiable S"
proof -
  have enum: "∃g. enumeration (g:: nat ⇒ 'a formula)"
    using countable_enumeration_formula by auto 
    let ?C = "{W:: 'a formula set.  ∀A. (A ⊆ W ∧ finite A) ⟶ satisfiable A}"
  have "consistenceP ?C"
    using ConsistenceCompactness by simp 
  moreover
  have "S ∈ ?C" using assms by simp
  ultimately 
  show "satisfiable S" using enum and Theo_ExistenceModels[of ?C S] by auto
qed 

end

