import Mathlib

/-!
Adapted from Conjectures.Goldbach.FinitePostBoundaryThrough32768 (kernel-checked primality
certificates for a finite list of numbers). Here the certificates are Pocklington witnesses:
each of the twelve large primes comes with a squarefree smooth factor set of its predecessor,
one base, and the two modular conditions, all checked by the kernel. The six pairs were found by
a congruence search; the obstruction half is uniform in k.
-/

namespace Conjectures.Goldbach.Rfc11Primorial757Repairs_aux

/-! ### small primality checkers that reduce in the kernel -/

def isPrimeSmall (p : ℕ) : Bool :=
  decide (2 ≤ p) && (List.range 28).all (fun m => decide (¬ (2 ≤ m ∧ m * m ≤ p ∧ m ∣ p)))

theorem prime_iff_isPrimeSmall (p : ℕ) (hp : p < 784) : Nat.Prime p ↔ isPrimeSmall p = true := by
  have hsq : Nat.sqrt p < 28 := (Nat.sqrt_lt' (m := p) (n := 28)).mpr (by omega)
  rw [isPrimeSmall, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · intro hpp
    refine ⟨hpp.two_le, ?_⟩
    intro m hm
    refine decide_eq_true (fun hcon => ?_)
    exact (Nat.prime_def_le_sqrt.mp hpp).2 m hcon.1 ((Nat.le_sqrt).mpr hcon.2.1) hcon.2.2
  · rintro ⟨h2, h⟩
    refine Nat.prime_def_le_sqrt.mpr ⟨h2, ?_⟩
    intro m hm2 hle hmd
    have hmem : m ∈ List.range 28 := List.mem_range.mpr (by omega)
    exact (of_decide_eq_true (h m hmem)) ⟨hm2, (Nat.le_sqrt).mp hle, hmd⟩

def isPrimeMid (p : ℕ) : Bool :=
  decide (2 ≤ p) && (List.range 1001).all (fun m => decide (¬ (2 ≤ m ∧ m * m ≤ p ∧ m ∣ p)))

theorem prime_iff_isPrimeMid (p : ℕ) (hp : p < 1002001) : Nat.Prime p ↔ isPrimeMid p = true := by
  have hsq : Nat.sqrt p < 1001 := (Nat.sqrt_lt' (m := p) (n := 1001)).mpr (by omega)
  rw [isPrimeMid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · intro hpp
    refine ⟨hpp.two_le, ?_⟩
    intro m hm
    refine decide_eq_true (fun hcon => ?_)
    exact (Nat.prime_def_le_sqrt.mp hpp).2 m hcon.1 ((Nat.le_sqrt).mpr hcon.2.1) hcon.2.2
  · rintro ⟨h2, h⟩
    refine Nat.prime_def_le_sqrt.mpr ⟨h2, ?_⟩
    intro m hm2 hle hmd
    have hmem : m ∈ List.range 1001 := List.mem_range.mpr (by omega)
    exact (of_decide_eq_true (h m hmem)) ⟨hm2, (Nat.le_sqrt).mp hle, hmd⟩

theorem primes_of_check {fs : List ℕ}
    (h : fs.all (fun r => decide (r < 1002001) && isPrimeMid r) = true) : ∀ r ∈ fs, Nat.Prime r := by
  intro r hr
  have h1 := List.all_eq_true.mp h r hr
  rw [Bool.and_eq_true, decide_eq_true_eq] at h1
  exact (prime_iff_isPrimeMid r h1.1).mpr h1.2


theorem coprimes_of_check {n a : ℕ} {fs : List ℕ}
    (h : fs.all (fun r => decide (Nat.Coprime (Nat.powMod a ((n - 1) / r) n - 1) n)) = true) :
    ∀ r ∈ fs, Nat.Coprime (Nat.powMod a ((n - 1) / r) n - 1) n := by
  intro r hr
  exact of_decide_eq_true (List.all_eq_true.mp h r hr)

/-! ### product of distinct primes -/

theorem prod_primes_dvd {fs : List ℕ} (hfs : ∀ r ∈ fs, Nat.Prime r) (hnd : fs.Nodup)
    {m : ℕ} (hm : ∀ r ∈ fs, r ∣ m) : fs.prod ∣ m := by
  induction fs with
  | nil => simp
  | cons b t ih =>
    rw [List.prod_cons]
    have hnd' := List.nodup_cons.mp hnd
    have hb : b ∣ m := hm b List.mem_cons_self
    have ht : t.prod ∣ m :=
      ih (fun r hr => hfs r (List.mem_cons_of_mem b hr)) hnd'.2
        (fun r hr => hm r (List.mem_cons_of_mem b hr))
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ hb ht
    rw [Nat.coprime_list_prod_right_iff]
    intro r hr
    have hrb : Nat.Prime r := hfs r (List.mem_cons_of_mem b hr)
    have hbb : Nat.Prime b := hfs b List.mem_cons_self
    have hne : b ≠ r := by
      intro h
      subst h
      exact hnd'.1 hr
    exact (Nat.Prime.coprime_iff_not_dvd hbb).mpr (by
      intro hd
      exact hne ((Nat.prime_dvd_prime_iff_eq hbb hrb).mp hd))

/-! ### Pocklington criterion -/

theorem pocklington {n a : ℕ} {fs : List ℕ}
    (hn : 1 < n) (hfs : ∀ r ∈ fs, Nat.Prime r) (hnd : fs.Nodup)
    (hdiv : fs.prod ∣ n - 1) (hbig : n < fs.prod * fs.prod)
    (ha : Nat.powMod a (n - 1) n = 1)
    (hg : ∀ r ∈ fs, Nat.Coprime (Nat.powMod a ((n - 1) / r) n - 1) n) :
    Nat.Prime n := by
  have hmod : a ^ (n - 1) ≡ 1 [MOD n] := by
    have h1 : a ^ (n - 1) % n = 1 % n := by
      rw [← Nat.powMod_def, ha, Nat.mod_eq_of_lt (by omega)]
    exact h1
  have keyr : ∀ r ∈ fs, ∀ p : ℕ, Nat.Prime p → p ∣ n → r ∣ p - 1 := by
    intro r hr p hp hpn
    have hrp : Nat.Prime r := hfs r hr
    have hrd : r ∣ n - 1 := (List.dvd_prod hr).trans hdiv
    have hmodp : a ^ (n - 1) ≡ 1 [MOD p] := hmod.of_dvd hpn
    have hnp : ¬ a ^ ((n - 1) / r) ≡ 1 [MOD p] := by
      intro hcon
      have hcop : Nat.Coprime (Nat.powMod a ((n - 1) / r) n - 1) p := by
        have h := hg r hr
        exact h.of_dvd_right hpn
      have hmod2 : p ∣ Nat.powMod a ((n - 1) / r) n - 1 := by
        have h1 : a ^ ((n - 1) / r) ≡ Nat.powMod a ((n - 1) / r) n [MOD n] := by
          rw [Nat.powMod_def]
          exact (Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))).symm
        have h2 := h1.of_dvd hpn
        exact (hcon.symm.trans h2).dvd'
      exact (hp.coprime_iff_not_dvd.mp hcop.symm) hmod2
    have : Fact p.Prime := ⟨hp⟩
    have hpa : (a : ZMod p) ≠ 0 := by
      intro h0
      have hz : (a : ZMod p) ^ (n - 1) = 0 := by
        rw [h0, zero_pow (by omega)]
      have h1 : (a : ZMod p) ^ (n - 1) = 1 := by
        simpa using (ZMod.natCast_eq_natCast_iff (a ^ (n - 1)) 1 p).mpr hmodp
      rw [hz] at h1
      exact one_ne_zero h1.symm
    let u : (ZMod p)ˣ := Units.mk0 (a : ZMod p) hpa
    have hu1 : u ^ (n - 1) = 1 := by
      apply Units.ext
      have hv : ((u : ZMod p)) = (a : ZMod p) := rfl
      rw [Units.val_pow_eq_pow_val, hv, Units.val_one]
      simpa using (ZMod.natCast_eq_natCast_iff (a ^ (n - 1)) 1 p).mpr hmodp
    have hu2 : u ^ ((n - 1) / r) ≠ 1 := by
      intro h1
      apply hnp
      have h2 := congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) h1
      rw [Units.val_pow_eq_pow_val] at h2
      have hv : ((u : ZMod p)) = (a : ZMod p) := rfl
      rw [hv, Units.val_one] at h2
      have h3 : ((a ^ ((n - 1) / r) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by simpa using h2
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h3
    have hd1 : orderOf u ∣ n - 1 := orderOf_dvd_of_pow_eq_one hu1
    have hd2 : ¬ orderOf u ∣ (n - 1) / r := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact hu2
    have hrd' : r ∣ orderOf u := by
      by_contra hne
      have hcop : Nat.Coprime r (orderOf u) := (Nat.Prime.coprime_iff_not_dvd hrp).mpr hne
      have hmul : n - 1 = r * ((n - 1) / r) := (Nat.mul_div_cancel' hrd).symm
      have hbad : orderOf u ∣ (n - 1) / r := by
        rw [hmul, mul_comm] at hd1
        exact hcop.symm.dvd_of_dvd_mul_right hd1
      exact hd2 hbad
    have hcard : orderOf u ∣ Fintype.card (ZMod p)ˣ := orderOf_dvd_card
    have htot : Fintype.card (ZMod p)ˣ = p - 1 := by
      rw [ZMod.card_units_eq_totient, Nat.totient_prime hp]
    exact hrd'.trans (by rw [← htot]; exact hcard)
  have key : ∀ p : ℕ, Nat.Prime p → p ∣ n → fs.prod ∣ p - 1 := by
    intro p hp hpn
    exact prod_primes_dvd hfs hnd (fun r hr => keyr r hr p hp hpn)
  have hpr : Nat.Prime n.minFac := Nat.minFac_prime (by omega)
  have hFpos : 0 < fs.prod := by
    rcases Nat.eq_zero_or_pos fs.prod with h0 | h
    · exfalso
      rw [h0] at hdiv
      have hz : n - 1 = 0 := Nat.eq_zero_of_zero_dvd hdiv
      omega
    · exact h
  have hmin : n.minFac = n := by
    by_contra hne
    have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
    have hlt : n.minFac < n := Nat.lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdvd) hne
    set m := n / n.minFac
    have hnb : n = n.minFac * m := by
      show n = n.minFac * (n / n.minFac)
      rw [mul_comm]
      exact (Nat.div_mul_cancel hdvd).symm
    have hne1 : m ≠ 1 := by
      intro h1
      rw [h1, Nat.mul_one] at hnb
      omega
    have hne0 : m ≠ 0 := by
      intro h0
      rw [h0, Nat.mul_zero] at hnb
      omega
    obtain ⟨q, hq, hqb⟩ := Nat.exists_prime_and_dvd hne1
    have hqn : q ∣ n := hqb.trans (show m ∣ n from Nat.div_dvd_of_dvd hdvd)
    have hFm : fs.prod ∣ n.minFac - 1 := key n.minFac hpr hdvd
    have hFq : fs.prod ∣ q - 1 := key q hq hqn
    have hmf2 : 2 ≤ n.minFac := hpr.two_le
    have hq2 : 2 ≤ q := hq.two_le
    have h1 : fs.prod ≤ n.minFac - 1 := Nat.le_of_dvd (by omega) hFm
    have h2 : fs.prod ≤ q - 1 := Nat.le_of_dvd (by omega) hFq
    have h3 : q ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hne0) hqb
    have h5 : (fs.prod + 1) * (fs.prod + 1) ≤ n.minFac * m :=
      Nat.mul_le_mul (by omega) (by omega)
    have h6 : fs.prod * fs.prod < (fs.prod + 1) * (fs.prod + 1) := by nlinarith
    omega
  rw [hmin] at hpr
  exact hpr

/-! ### the primorial through 757 -/

theorem hfilter : (Finset.range 758).filter Nat.Prime =
    (Finset.range 758).filter (fun p => isPrimeSmall p = true) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hp, hpp⟩
    exact ⟨hp, (prime_iff_isPrimeSmall p (by omega)).mp hpp⟩
  · rintro ⟨hp, h⟩
    exact ⟨hp, (prime_iff_isPrimeSmall p (by omega)).mpr h⟩

private def fs1_1 : List ℕ := [2, 4909, 10007, 18451, 18979, 92821, 129121, 167149, 190979, 222349, 290497, 293357, 307129, 310727, 368833, 369709, 373339, 428251, 458599, 628973, 683737, 777277, 824651, 826831, 883391, 952117, 952199, 956341, 984121, 995303]
private def fs2_1 : List ℕ := [2, 16921, 30467, 85243, 145601, 152533, 155081, 286477, 386039, 405611, 415273, 424709, 556373, 618041, 619111, 643273, 651649, 695573, 760499, 794141, 803897, 846673, 875339, 908857, 908881, 959921, 980773, 981289, 996173]
private def pk_1 : ℕ := 1434385450674124922089992203171968534701839542213095931316337323868077302988013578078155648374163953551206968618642028262851366509391474024341056331476631334672627750069524226174873718269807175631549491658716166247846563104738244446989678498408135791631812496246026195943331107526875469254753473958554817938197489339
private def qk_1 : ℕ := 216431254073632532887303869330531448435506925568057006641051519777439283748457970360158102418380808148359729256396404284531533686844992983679853813229318584318911661416051417577790877858609674605232545668211718385391580128541080439916963873509078829919954640573328646233810803916743056110359000428808890164309723631
set_option maxRecDepth 400000 in
private theorem prime_p_1 : Nat.Prime pk_1 :=
  pocklington (n := pk_1) (a := 2) (fs := fs1_1) (by decide) (primes_of_check (by decide))
    (by decide) (by decide) (by decide) (by decide) (coprimes_of_check (by decide))
set_option maxRecDepth 400000 in
private theorem prime_q_1 : Nat.Prime qk_1 :=
  pocklington (n := qk_1) (a := 3) (fs := fs2_1) (by decide) (primes_of_check (by decide))
    (by decide) (by decide) (by decide) (by decide) (coprimes_of_check (by decide))

private def fs1_2 : List ℕ := [2, 281, 47917, 66457, 76207, 105533, 105601, 227497, 230101, 244481, 250967, 266351, 274951, 322649, 343193, 368327, 387187, 482513, 508709, 577463, 641419, 644257, 679957, 710779, 751133, 809447, 823717, 886339, 896327, 926867]
private def fs2_2 : List ℕ := [2, 10909, 25447, 75797, 85303, 104479, 109537, 171007, 177539, 214733, 251831, 277247, 281081, 307939, 312383, 328177, 332573, 336961, 374441, 491851, 497633, 501173, 536189, 596273, 636541, 645383, 658321, 875893, 939193, 945809]
private def pk_2 : ℕ := 2999027971519781708875309230580862344067458135371091436507528437140907956071180566221656581794248818584738055127307166538486864239225752967781833762207108217952167839382019679854940226284829980797421552608737010339174140695988078717395139802164113149000006964303800922519311482389106561426933821072675469470005409333
private def qk_2 : ℕ := 302605437975733201079282914424137622207234800191214439407249250150125217401762530654970919790840704814395340622769698556278936153247181048259986527204791620030910983589131607650388965972003719676142522045118758927302145770570571056418144941670316094103527309334908761834972340498130489303291127702051946735009016607
set_option maxRecDepth 400000 in
private theorem prime_p_2 : Nat.Prime pk_2 :=
  pocklington (n := pk_2) (a := 2) (fs := fs1_2) (by decide) (primes_of_check (by decide))
    (by decide) (by decide) (by decide) (by decide) (coprimes_of_check (by decide))
set_option maxRecDepth 400000 in
private theorem prime_q_2 : Nat.Prime qk_2 :=
  pocklington (n := qk_2) (a := 5) (fs := fs2_2) (by decide) (primes_of_check (by decide))
    (by decide) (by decide) (by decide) (by decide) (coprimes_of_check (by decide))

private def fs1_3 : List ℕ := [2, 317, 10007, 28087, 64153, 102913, 150901, 169307, 191537, 214943, 261031, 303593, 365851, 383107, 396541, 437959, 581701, 638489, 643429, 673193, 754279, 773021, 794071, 810259, 812359, 871919, 889037, 904619, 922613, 941489]
private def fs2_3 : List ℕ := [2, 643, 65269, 71867, 76163, 85429, 117389, 121711, 143617, 151607, 191519, 198593, 263537, 308551, 318181, 427733, 491003, 569263, 596579, 618913, 699299, 702349, 771553, 792551, 799489, 845881, 867263, 877267, 916183, 954991]
private def pk_3 : ℕ := 3076361274836321973542523226278017226567510005709642050850101200565198475191425144631310656249332821813580496339284151871643220135815328357132147832324724398028858549881583456455353292143589966585634896340833645530306523409847483540699278301456229117476915221311535428262631522078516360937788487983616976586510823781
private def qk_3 : ℕ := 1876088839406950391389364991229482722844529397633816763022065330371351285017989500683630596128301463285119597285831145770505480452894072666930582601793125358945759684575143474802640496241660584124711215639950008369407906289990491120020648814295414747178386189146529098268794212252339215157548935178474147721010815129
set_option maxRecDepth 400000 in
private theorem prime_p_3 : Nat.Prime pk_3 :=
  pocklington (n := pk_3) (a := 2) (fs := fs1_3) (by decide) (primes_of_check (by decide))
    (by decide) (by decide) (by decide) (by decide) (coprimes_of_check (by decide))
set_option maxRecDepth 400000 in
private theorem prime_q_3 : Nat.Prime qk_3 :=
  pocklington (n := qk_3) (a := 3) (fs := fs2_3) (by decide) (primes_of_check (by decide))
    (by decide) (by decide) (by decide) (by decide) (coprimes_of_check (by decide))

private def fs1_4 : List ℕ := [2, 521, 10007, 45197, 51343, 59611, 156841, 207619, 226789, 272009, 272989, 273131, 277231, 315949, 428221, 438241, 539153, 579949, 649471, 661121, 665381, 809747, 814823, 815527, 838441, 841921, 893359, 911951, 916471, 920741]
private def fs2_4 : List ℕ := [2, 6737, 10009, 41969, 50123, 92237, 117709, 158759, 191669, 216113, 233143, 255259, 311021, 320113, 329969, 409289, 438661, 471089, 517577, 541589, 665747, 681061, 739003, 740429, 811619, 821081, 828673, 846343, 864211, 865871]
private def pk_4 : ℕ := 2870649510187229652617645074757507562024146532467506649067616293755314016418811573707208387507842760997448475777448456084753012257262995170647360014049240413988148313193330953826486359481766436580466927484938014343228074692672078906846957598715464954049707063291622794366332946520369062346459882058908352659715994551
private def qk_4 : ℕ := 3732617308803800167291539215252492370525239338657105102761939080826752330527074620046046615662336285800818315722705274104778588527682872861436280564774559261978009332748971621184172025031900964366661221822773524189724498240445220640779611888953393532157361483985796574342234699254105039113990015490546479750312857329
set_option maxRecDepth 400000 in
private theorem prime_p_4 : Nat.Prime pk_4 :=
  pocklington (n := pk_4) (a := 3) (fs := fs1_4) (by decide) (primes_of_check (by decide))
    (by decide) (by decide) (by decide) (by decide) (coprimes_of_check (by decide))
set_option maxRecDepth 400000 in
private theorem prime_q_4 : Nat.Prime qk_4 :=
  pocklington (n := qk_4) (a := 3) (fs := fs2_4) (by decide) (primes_of_check (by decide))
    (by decide) (by decide) (by decide) (by decide) (coprimes_of_check (by decide))

private def fs1_5 : List ℕ := [2, 701, 40531, 64783, 67867, 70351, 144383, 196499, 259603, 270241, 340579, 348389, 353641, 357353, 393103, 408923, 441349, 448193, 455537, 464917, 468371, 479441, 492967, 728869, 749153, 789533, 840727, 846943, 859559, 899719]
private def fs2_5 : List ℕ := [2, 13859, 19427, 24197, 34367, 47881, 71503, 105727, 190891, 265169, 299567, 340169, 364687, 396349, 448853, 461059, 462713, 481787, 545551, 585593, 596227, 599561, 600557, 671501, 723803, 739069, 864803, 893041, 915191, 935839]
private def pk_5 : ℕ := 899387004124939489926693130872146326128217155568148348906697263022587175928720208013640226401296383707799036581875726615133805466608672499896629726654562805724975202331043159531856142239650715071804313785438461767268274585601208317997502155537020329625504450027770495170091641500784069773836923441182034868951037617
private def qk_5 : ℕ := 7354696519613847784959787231640353589558515183337616340880246955204995757753637534177928527561427424790034452793316436121780695514573662540207920996875186789232721855096835059231466838402433536112105872849200961398922441580795416116535709704049052778133331234069003715715617915717308557051725448495636505643585027233
set_option maxRecDepth 400000 in
private theorem prime_p_5 : Nat.Prime pk_5 :=
  pocklington (n := pk_5) (a := 5) (fs := fs1_5) (by decide) (primes_of_check (by decide))
    (by decide) (by decide) (by decide) (by decide) (coprimes_of_check (by decide))
set_option maxRecDepth 400000 in
private theorem prime_q_5 : Nat.Prime qk_5 :=
  pocklington (n := qk_5) (a := 3) (fs := fs2_5) (by decide) (primes_of_check (by decide))
    (by decide) (by decide) (by decide) (by decide) (coprimes_of_check (by decide))

private def fs1_6 : List ℕ := [2, 659, 17317, 23099, 108881, 140773, 183907, 203317, 220859, 254147, 273773, 329657, 364669, 415879, 435139, 472253, 485647, 485701, 493967, 556693, 570961, 607129, 609757, 642527, 658199, 671537, 751787, 765209, 952247, 985571]
private def fs2_6 : List ℕ := [2, 257, 10009, 16319, 44351, 69761, 123727, 128389, 215261, 294859, 311687, 376709, 432121, 499691, 516979, 522689, 539687, 635729, 664043, 680809, 776221, 839471, 878551, 884057, 908137, 924299, 946667, 961033, 976117, 984337]
private def pk_6 : ℕ := 7244245400245155185938791299604956911645542644137506338650521947676752267316064369768903371395946337248701442531026349597125922453779127996174845289074940519159740202650341049628067977210312184085759937933688033207660798573213472691100394921625041255932167927248169725918052475842395033779202657441162246786809069867
private def qk_6 : ℕ := 2660654828241389543924985135410042987178536162549411289093811114196347253102764920860979133359322232948698744719204245687171478723639674051950615579160758994789496266263112812887919599560188917334932286027879274591768060826462476630339459309878246473378434893667959327144798992819316118411472188883020001828234207953
set_option maxRecDepth 400000 in
private theorem prime_p_6 : Nat.Prime pk_6 :=
  pocklington (n := pk_6) (a := 2) (fs := fs1_6) (by decide) (primes_of_check (by decide))
    (by decide) (by decide) (by decide) (by decide) (coprimes_of_check (by decide))
set_option maxRecDepth 400000 in
private theorem prime_q_6 : Nat.Prime qk_6 :=
  pocklington (n := qk_6) (a := 3) (fs := fs2_6) (by decide) (primes_of_check (by decide))
    (by decide) (by decide) (by decide) (by decide) (coprimes_of_check (by decide))

set_option maxRecDepth 400000 in
theorem primorial757 : (∏ p ∈ (Finset.range 758).filter Nat.Prime, p) = 1650816704747757454977296072502499983137346467781152937957388843645516586736471548438313750792544761699566697875038432547382900196236467008020910144705949918991539411485575643752664596128416850236782037326927884633238143233279324886906642371917214621551767136819354842177141911443618525365112474387363708102507212970 := by
  rw [hfilter]
  decide

end Conjectures.Goldbach.Rfc11Primorial757Repairs_aux

open Conjectures.Goldbach.Rfc11Primorial757Repairs_aux

theorem Conjectures.Goldbach.Rfc11Primorial757Repairs : let W := ∏ p ∈ (Finset.range 758).filter Nat.Prime, p; 6*W < 10^316 ∧ (10:ℕ)^316 < 7*W ∧ (∀ k : ℕ, 1≤k → k≤6 → let n := k*W; (∀ p≤757, p.Prime → ¬ (n-p).Prime) ∧ (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n)) := by
  intro W
  have hW : W = 1650816704747757454977296072502499983137346467781152937957388843645516586736471548438313750792544761699566697875038432547382900196236467008020910144705949918991539411485575643752664596128416850236782037326927884633238143233279324886906642371917214621551767136819354842177141911443618525365112474387363708102507212970 := primorial757
  refine ⟨?_, ?_, ?_⟩
  · rw [hW]; decide
  · rw [hW]; decide
  · intro k hk1 hk6 n
    have hn : n = k * W := rfl
    have hobs : ∀ p ≤ 757, Nat.Prime p → ¬ (n - p).Prime := by
      intro p hp hpp
      have hpW : p ∣ W :=
        Finset.dvd_prod_of_mem (fun q : ℕ => q)
          (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpp⟩)
      have hpk : p ∣ k * W := hpW.mul_left k
      have hpd : p ∣ n - p := by
        rw [hn]
        exact Nat.dvd_sub hpk (dvd_refl p)
      have hbig : p < n - p := by
        have hW2 : 2310 ≤ W := by rw [hW]; norm_num
        have hkW : W ≤ k * W := by simpa using Nat.mul_le_mul_right W hk1
        rw [hn]; omega
      intro hq
      have hpeq : p = n - p := (Nat.prime_dvd_prime_iff_eq hpp hq).mp hpd
      omega
    have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨hobs, ⟨pk_1, qk_1, prime_p_1, prime_q_1, by rw [hn, hW]; decide⟩⟩
    · exact ⟨hobs, ⟨pk_2, qk_2, prime_p_2, prime_q_2, by rw [hn, hW]; decide⟩⟩
    · exact ⟨hobs, ⟨pk_3, qk_3, prime_p_3, prime_q_3, by rw [hn, hW]; decide⟩⟩
    · exact ⟨hobs, ⟨pk_4, qk_4, prime_p_4, prime_q_4, by rw [hn, hW]; decide⟩⟩
    · exact ⟨hobs, ⟨pk_5, qk_5, prime_p_5, prime_q_5, by rw [hn, hW]; decide⟩⟩
    · exact ⟨hobs, ⟨pk_6, qk_6, prime_p_6, prime_q_6, by rw [hn, hW]; decide⟩⟩
