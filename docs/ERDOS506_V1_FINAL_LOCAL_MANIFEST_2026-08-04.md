> **SUPERSEDED W CZĘŚCI `n=6` (2026-08-10).** Wartość `f_V1(6)=9` i
> przypięty do niej dowód są fałszywe; poprawna wartość to `8`. Zobacz
> [ścisłą korektę](ERDOS506_N6_CORRECTION_2026-08-10.md). Poniższy manifest
> pozostaje niezmienionym historycznym zapisem poza tym bannerem.

# Erdős #506 — końcowy lokalny manifest wariantu V1

Data: 2026-08-04.

Status operacyjny:

~~~text
CLOSED_LOCAL_LEDGER_V1__EXTERNAL_REVIEW_OPEN
~~~

Ten dokument zastępuje wcześniejsze snapshoty mówiące, że okno
n=11,...,14 albo jedna z sześciu gałęzi maksymalnego okręgu pozostaje
otwarta. Wiąże końcowe raporty z konkretnymi hashami i rozdziela trzy różne
poziomy twierdzeń:

1. domknięcie matematyczne w lokalnym ledgerze;
2. odtwarzalność przez obecne checkery;
3. gotowość publikacyjna i niezależna recenzja.

Pierwszy poziom jest zamknięty jako lokalny ledger. Aktywny DAG dolnych
granic nie używa przeszukiwania konfiguracji, katalogów supportów lub orbit,
SAT/ILP ani klasyfikacji skończonych podgrup. Dawne replaye są niezależnymi
kontrolami historycznymi. Checkery nowych gałęzi sprawdzają jawne
tożsamości, współczynniki i małe rachunki symboliczne; kompletność dostarczają
teksty dowodów. Trzeci poziom nadal wymaga pracy. Status powyżej nie jest
deklaracją publikacyjnego, niezależnie potwierdzonego ani pierwszego na
świecie rozwiązania.

## 1. Dokładna teza

Manifest dotyczy wyłącznie konwencji V1:

~~~text
P jest zbiorem n różnych punktów rzeczywistej płaszczyzny;
nie wszystkie punkty leżą na jednej prostej;
nie wszystkie punkty leżą na jednym okręgu;
liczymy różne właściwe okręgi przechodzące przez niewspółliniową trójkę P;
prostych nie liczymy jako okręgów.
~~~

Nie jest to automatycznie rozwiązanie silniejszego wariantu V3 z zakazem
trzech współliniowych punktów.

Niech

~~~text
F(n)=1+binom(n-1,2)-floor((n-1)/2).
~~~

Końcowy lokalny wynik brzmi:

~~~text
f_V1(4),...,f_V1(10) = 3,5,9,11,17,25,33,
f_V1(n)=F(n) dla każdego n>=9.
~~~

Wiersz ten jest tezą zamkniętego lokalnego ledgera. Dla `n=9` aktywną
podstawą jest teraz dowód analityczny obejmujący wszystkie rozmiary
największego okręgu `3,...,8`; dawny pakiet solverowy pozostaje niezależną
kontrolą historyczną. Dokładną granicę zaufania opisuje sekcja 7.

W szczególności:

~~~text
f_V1(11)=41,
f_V1(12)=51,
f_V1(13)=61,
f_V1(14)=73,
f_V1(15)=85,
f_V1(16)=99.
~~~

Jedynymi wyjątkami od F w naturalnym zakresie n>=4 są:

~~~text
f_V1(7)=11 zamiast F(7)=13,
f_V1(8)=17 zamiast F(8)=19.
~~~

## 2. Konstrukcje górne

Dla n=4,5,6 oraz każdego n>=9 wystarcza standardowa konstrukcja:
n-1 punktów na okręgu, z maksymalną liczbą par antypodycznych, oraz środek
tego okręgu. Daje ona dokładnie F(n) właściwych okręgów.

Dla n=7 używa się trójkąta równobocznego, środków jego boków i centroidu;
konfiguracja wyznacza 11 okręgów. Dla n=8 repo zawiera jawną wymierną
konfigurację z 17 okręgami i samodzielny pakiet certyfikatów.

Źródła konstrukcji i ich kontroli:

~~~text
docs/erdos506_upper_bound_front_2026-06-23.md
docs/ERDOS506_N7_F11_PROOF_2026-07-30.md
reports/ERDOS506_N8_F17_CERTYFIKAT_2026-07-30_PL.md
artifacts/erdos-506-n8-f17/
~~~

## 3. Pokrycie dolnych granic

### 3.1. Zakres n=4,...,10

Pokrycie małych wartości prowadzą kolejno:

~~~text
n=4,5  docs/ERDOS506_V1_COMPLETE_PROOF_2026-08-04.md, sekcje 6.1--6.2
n=6    docs/ERDOS506_N6_F9_ANALYTIC_PROOF_2026-08-04.md
n=7    docs/ERDOS506_N7_F11_PROOF_2026-07-30.md
n=8    docs/ERDOS506_N8_F17_ANALYTIC_PROOF_2026-08-04.md
n=9    scratch/n9_analytic_closure_20260804/FULL_THEORETICAL_PROOF.md
       scratch/n9_analytic_closure_20260804/GAMMA4_ORCHARD_CLOSURE.md
       scratch/n9_analytic_closure_20260804/GAMMA5_ANALYTIC_CLOSURE.md
       scratch/n9_analytic_closure_20260804/INDEPENDENT_REDTEAM.md
       docs/ERDOS506_N9_LOCAL_CLOSURE_2026-07-30.md  [ścieżka historyczna]
n=10   scratch/n10_n11_low_hanging_analytic_20260804/N10_GAMMA4_FINAL_ANALYTIC_CLOSURE.md
       scratch/n10_gamma5_analytic_closure_20260804/REPORT.md
       docs/ERDOS506_GAMMA6_X4_UNCONDITIONAL_BOUND_2026-07-30.md
       scratch/global_zero_bruteforce_audit_20260804/BRIDGE_SUPPLEMENT.md
       docs/ERDOS506_N10_FINAL_EXACT_CLOSURE_2026-08-01.md [ścieżka historyczna]
~~~

Spójny dowód analityczny dla `n=4,...,9` oraz dokładny DAG zależności dla
`n=10` są obecnie zebrane także w:

~~~text
docs/ERDOS506_V1_COMPLETE_PROOF_2026-08-04.md
scratch/n9_analytic_closure_20260804/REPORT.md
scratch/n9_analytic_closure_20260804/verify_symbolic.py
scratch/final_paper_redteam_20260804/SMALL_AND_INFINITE_DEPENDENCY_AUDIT.md
scratch/final_paper_redteam_20260804/CERTIFICATION_GAP_AUDIT.md
~~~

Stary katalog pivot-SG dla `n=7` jest tylko kontrolą historyczną. Miał
błędny próg dla trójprostej przechodzącej przez punkt inwersji; poprawny
rachunek pozostawia 3635 wzorców w 10 orbitach zamiast 2660 w 7. Nie wpływa
to na nowy analityczny dowód `f_V1(7)=11`.

Analogicznie pakiety `erdos506_small_n_incidence_audit_2026-06-23.md`,
`erdos506_n6_survivor_geometry_2026-06-23.md` i SAT-owa dolna granica z
raportu `n=8` są kontrolami historycznymi, nie przodkami powyższego DAG-u.
Wyznacznikowy audyt `n=8` pozostaje kontrolą jawnej konstrukcji górnej.
Niezależny strict audit całego zakresu znajduje się w
`scratch/small_n4_n9_zero_bf_audit_20260804/REPORT.md`.

### 3.2. Redukcja okna n=11,...,14

Kompletność redukcji do sześciu końcowych gałęzi jest opisana w:

~~~text
docs/ERDOS506_COMPLETE_SOLUTION_ROADMAP_2026-08-02.md
docs/ERDOS506_FINITE_SMALL_CIRCLE_FARKAS_2026-07-30.md
~~~

Gałęzie mniejszych maksymalnych okręgów zamykają dokładne duale Farkasa,
a większe maksymalne okręgi usuwa rich-circle pencil bound. Po tych
redukcjach pozostawało dokładnie:

~~~text
(11,Gamma5), (12,Gamma5),
(13,Gamma5), (13,Gamma6),
(14,Gamma5), (14,Gamma6).
~~~

Stan końcowy każdej gałęzi centralnej:

1. `n=11,Gamma5`. Lenchner plus delecja dają bez katalogu `C>=36`;
   warstwy `C=36,37` zamyka raport low-hanging, `C=38` marginalny rachunek
   luzu i krótka redukcja wybranego `Gamma`, a `C=39,40` argumenty
   analityczne. Nowy lemat linkowy usuwa oba dawne importy Dumnickiego.
   Zbiorczy strict audit ma all-paper DAG.
2. `n=11,Gamma6`. F1/F2 i jedno zaokrąglenie CG zamykają `C<=38`;
   `scratch/n11_gamma6_uniform_boundary_20260804/REPORT.md` zamyka `C=39,40`
   jednym argumentem footprintowym. Dwa niezależne red-teamy zwróciły PASS.
3. `n=12,Gamma5`. Dokument
   `docs/ERDOS506_N12_GAMMA5_ANALYTIC_CLOSURE_2026-08-04.md` wyklucza
   wszystkie `C<=50` bez przeglądu supportów; szczegóły są w sekcji 3.3.
4. `n=12,Gamma6`. Raport analityczny wyklucza wszystkie `1<=B6<=4`.
   Red-team znalazł fałszywą minimalizację momentu dla
   `B6=2,s=2,B5=6`; zastąpiono ją rachunkiem współincydencji `6<8`, a
   ponowna recenzja zwróciła VALID. Stary replay jest tylko kontrolą.
5. `n=13,Gamma5`. Added-center global closure i mocny transfer dają `C>=61`.
6. `n=13,Gamma6`. Raporty pokrywają rozłącznie `W<=47`, `W=48`,
   `W=49,...,51` i `W=52,...,54`; kap sygnatur daje `W<=54`.
7. `n=14,Gamma5`. Mocny transfer daje `C>=74`, więcej niż potrzeba.
8. `n=14,Gamma6`. Added-center global dual daje `C>=73` bez katalogowania
   końcowych profili.

Małe i duże wartości maksymalnego okręgu zamykają odpowiednio jawne duale
rozmiarowe i lemata pękowe, więc lista ta nie pomija żadnego rozmiaru.

### 3.3. Pełny łańcuch n=12,Gamma5

Eliminacja współczynnikowa pokrywa C<=44. Następnie:

~~~text
C=45,46,47  STRONG_GAMMA5_TRANSFER.md, sekcja 7
C=48        obtuse-vector plus Gram-rank closure
C=49        inversion/parity closure
            plus niezależny defect-determinant audit
C=50        globalny most redukuje do B6=0, K=B5, L=14
            five-line q+z closure usuwa L5=1
            q>=0 zostawia dokładnie sześć endpointów (L4,B5)
            pięć endpointów zamykają parity i H2K8
            endpoint (0,8) redukuje się do trzech profili
            każdy profil zawiera Type A
            gallery/Hall obstruction usuwa Type A
~~~

Główne pliki tego łańcucha:

~~~text
scratch/added_center_melchior_transfer_20260804/STRONG_GAMMA5_TRANSFER.md
scratch/added_center_melchior_transfer_20260804/N12_GAMMA5_C48_C50_ANALYTIC_BRIDGE.md
scratch/n12_gamma5_c48_obtuse_gram_closure_20260804/REPORT.md
scratch/n12_gamma5_fourway_inversion_geometry_20260804/REPORT.md
scratch/n12_gamma5_c49_defect_determinant_closure_20260804/REPORT.md
scratch/n12_c50_l14_fiveline_qz_closure_20260804/REPORT.md
scratch/added_center_melchior_transfer_20260804/INDEPENDENT_C50_L14_ENDPOINT_UNION_AUDIT.md
scratch/added_center_melchior_transfer_20260804/N12_C50_KAPPA_PARITY_CLOSURE.md
scratch/added_center_melchior_transfer_20260804/N12_C50_L14_H2K8_CLOSURE.md
scratch/n12_c50_typeA_gallery_hall_obstruction_20260804/REPORT.md
scratch/n12_c50_typeA_gallery_hall_obstruction_20260804/INDEPENDENT_TOPOLOGY_AND_TRANSFER_AUDIT.md
~~~

### 3.4. Zakres n>=15

Lokalna baza `f_V1(15)=85` używa bezkatalogowych zamknięć added-center dla
`Gamma5` i `Gamma6`. Ścisła analiza endpointu siedmioprostej zastępuje
twierdzenie Zhanga, a argument sygnatur zastępuje klasyfikację Cuntza.
`Gamma7` ma funkcjonał `37166/441>84`; nierówność
`W+6N_(1,6)<=84` wynika z matchingowego supportu i elementarnego kapu trzech
centrów. Kap daje porządek cykliczny oraz normalna postać jednej macierzy
rzędu sześć, bez klasyfikacji `PGL_2(R)` i bez replayu 76 matchingów.
Pozostaje jawne klasyczne wejście Lenchnera.

Endpoint `n=16` jest obsłużony przez ray-packing. Lemat krytycznej delecji
jawnie sprawdza, że po usunięciu wybranego punktu pozostaje konfiguracja V1,
a deletion lemma propaguje wynik dla każdego `n>=17`. Bezpośredni dowód
`n>=40` jest dodatkową kontrolą, nie koniecznym ogniwem.

Dokument `n=16` został rozszerzony o jawne współczynniki wszystkich siedmiu
duali dla `m=3,...,9`. Nie zmieniło to tezy: audyt zwraca `status=passed`, a
najsłabszy wiersz `m=6` nadal daje `20041/204>98` bez optymalizatora.

~~~text
scratch/n15_gamma5_gamma6_added_center_closure_20260804/REPORT.md
scratch/n15_gamma5_gamma6_added_center_closure_20260804/verify_symbolic.py
tests/test_erdos506_n15_gamma5_gamma6_added_center_closure.py
scratch/n15_gamma7_zero_bf_audit_20260804/REPORT.md
scratch/n15_gamma7_zero_bf_audit_20260804/verify_symbolic.py
scratch/added_center_melchior_transfer_20260804/STRONG_GAMMA5_TRANSFER.md
scratch/global_zero_bruteforce_audit_20260804/REPORT.md
scratch/global_zero_bruteforce_audit_20260804/BRIDGE_SUPPLEMENT.md
docs/ERDOS506_N14_N15_GAMMA7_SUPPORT_2026-07-31.md [historyczny funkcjonał]
docs/ERDOS506_N16_DELETION_RAY_PACKING_2026-07-31.md
erdos506_n16_deletion_ray_packing_audit.py
tests/test_erdos506_n16_deletion_ray_packing_audit.py
docs/ERDOS506_DELETION_LEMMA_N17_2026-07-30.md
~~~

Starsze raporty `ERDOS506_N15_GAMMA5_SIMPLICIAL_PIVOT_CLOSURE` i
`ERDOS506_N15_GAMMA6_SIMPLICIAL_PIVOT_CLOSURE` pozostają niezależną ścieżką
historyczną, lecz nie należą już do aktywnego korzenia dowodu.

## 4. Rozliczenie sześciu wierszy red-teamu przy C=50

Końcowy audyt global-dual wskazał sześć wierszy, których nie usuwały same
starsze pliki Type-A:

~~~text
(34,19,11;14,0,0;11,17)
(34,19,11;13,1,0;11,10)
(36,16,12;14,0,0;12,18)
(36,16,12;13,1,0;12,11)
(36,16,12;12,2,0;12, 4)
(36,16,12;13,0,1;12, 2)
~~~

Była to rzeczywista luka interfejsu starszego transferu, ale nie
kontrprzykład geometryczny. Późniejsze pliki naprawiają dokładnie ten punkt.

Dla pierwszych pięciu wierszy L5=0 i punktowo q>=0, podczas gdy dokładne
sumy globalne wynoszą:

~~~text
-1, -2, -2, -3, -4.
~~~

Dla szóstego wiersza L5=1 i punktowo q+z>=0, lecz:

~~~text
sum q=-9,
sum z=5,
sum(q+z)=-4.
~~~

Stare świadki skalarne osiągały ujemne wartości przez lokalny stan

~~~text
(d3,d4,d5)=(10,3,6).
~~~

Nowy lemat siatki dowodzi d3=10 => d5<=5. Po inwersji sześć 4-prostych
musiałoby tworzyć dwa pęki i siatkę 3 x 3, a trzy dodatkowe 3-proste
musiałyby być trzema transwersalami. Rzeczywista siatka 3 x 3 ma najwyżej
dwie takie transwersale, bo odpowiadają one afinicznym bijekcjom dwóch
rzeczywistych zbiorów trójelementowych.

Autor audytu, który znalazł sześć wierszy, ponownie sprawdził oba nowe
pliki, zmapował każdy wiersz na powyższe sumy i zwrócił werdykt PASS.
Rekoncyliacja jest także dodana do:

~~~text
scratch/n12_gamma5_fourway_global_dual_20260804/REPORT.md
scratch/n12_gamma5_fourway_global_dual_20260804/global_dual_audit.py
~~~

## 5. Odtworzone checkery kluczowych gałęzi

W dniu manifestu uruchomiono:

~~~powershell
python scratch\n9_analytic_closure_20260804\verify_symbolic.py
python scratch\n9_analytic_closure_20260804\verify_concyclic_branch.py
python scratch\n10_gamma5_analytic_closure_20260804\verify_symbolic.py
python scratch\n11_gamma5_c38_k8_short_reduction_redteam_20260804\verify_symbolic.py
python scratch\n11_gamma6_uniform_boundary_20260804\verify_exact.py
python scratch\n12_gamma5_c48_obtuse_gram_closure_20260804\verify_exact.py
python scratch\n12_gamma5_fourway_inversion_geometry_20260804\verify_exact.py
python scratch\n12_gamma5_c49_defect_determinant_closure_20260804\verify_exact.py
python scratch\n12_c50_l14_fiveline_qz_closure_20260804\verify_exact.py
python scratch\n12_c50_typeA_gallery_hall_obstruction_20260804\verify_symbolic.py
python scratch\n12_gamma6_analytic_closure_20260804\verify_repaired_endpoint.py
python scratch\n13_gamma5_added_center_global_closure_20260804\verify_symbolic.py
python scratch\n13_gamma6_high_weight_event_capacity_closure_20260804\verify_equations.py
python scratch\n14_gamma6_added_center_global_dual_20260804\verify_symbolic.py
python scratch\n15_gamma5_gamma6_added_center_closure_20260804\verify_symbolic.py
python scratch\n15_gamma7_zero_bf_audit_20260804\verify_symbolic.py
python erdos506_n16_deletion_ray_packing_audit.py
python -m pytest -q tests\test_erdos506_n16_deletion_ray_packing_audit.py
~~~

Wyniki:

~~~text
PASS_N9_FULL_ANALYTIC_SYMBOLIC_AUDIT
PASS_N9_GAMMA5_CONCYCLIC_ALGEBRA
PASS_N10_GAMMA5_C32_K2_SYMBOLIC
PASS_SYMBOLIC_N11_GAMMA5_C38_K8_SHORT_REDUCTION
PASS_N11_GAMMA6_UNIFORM_C39_C40_IDENTITIES
PASS_N12_GAMMA5_C48_OBTUSE_GRAM_CLOSURE
PASS_N12_GAMMA5_C49_INVERSION_PARITY_CLOSURE
PASS_N12_GAMMA5_C49_DEFECT_DETERMINANT_CLOSURE
PASS_N12_C50_L14_FIVELINE_QZ_CLOSURE
PASS_SYMBOLIC_N12_C50_TYPEA_GALLERY_HALL
PASS_N12_GAMMA6_REPAIRED_S2_K6_ENDPOINT
PASS_SYMBOLIC_N13_GAMMA5_ADDED_CENTER_GLOBAL_CLOSURE
PASS: all equations (4.3)--(4.10) have exact QQ certificates
PASS_SYMBOLIC_N14_GAMMA6_ADDED_CENTER_GLOBAL_DUAL
PASS_N15_GAMMA5_GAMMA6_ADDED_CENTER_CATALOGUE_FREE_CLOSURE
PASS_N15_GAMMA7_ZERO_BF_SYMBOLIC
N16 deletion ray-packing: status=passed
N16 focused pytest: 3 passed
~~~

Pełne polecenie `python -m pytest -q tests` zakończyło pierwszy przebieg po
1733.16 s wynikiem:

~~~text
714 passed, 21 failed, 8 errors, 1 skipped
~~~

Nie był to czysty PASS. Diagnostyka rozdzieliła awarie na zmienione piny
hashy wspólnego generatora, historyczny skaner zbierający nowe JSON-y,
niezaktualizowany test po poprawie progu `n=7` oraz jedno rzeczywiste
nadmierne roszczenie agregatora `n=13,Gamma6`. Po semantycznym replayu
przepięto wyłącznie te źródła, których wynik matematyczny pozostał identyczny;
skaner `n=12` dostał jawny manifest 11 wejść, próg `n=7` skorygowano, a
certyfikat jednego słowa `n=13` nie jest już promowany do 48 przypisań.

Po pierwszej serii poprawek drugi pełny przebieg dał
`739 passed, 5 failed, 1 skipped`: trzy awarie były nieaktualnym łańcuchem
proweniencji, a dwie wyciekiem `CIRCLE_COUNT=72` do testu C70. Po odświeżeniu
artefaktów i pinów trzeci przebieg dał `742 passed, 2 failed, 1 skipped`;
pozostały wyłącznie dwa objawy tego samego wycieku stanu. Dokładna regresja
`Gate0 -> C70` po izolacji inwariantu zakończyła się `8 passed`.

Finalne polecenie `python -m pytest -q` używa teraz jawnego `testpaths=tests`
i zakończyło się kodem zero:

~~~text
744 passed, 1 skipped in 1900.75s (0:31:40)
~~~

Historyczne testy pod `scratch/` nie są częścią domyślnego zestawu, lecz
pozostają uruchamialne przez podanie ich ścieżki. Wcześniejsze FAIL-e są
zachowane powyżej jako historia diagnostyczna, a nie przedstawiane jako PASS.

## 6. Wiązanie SHA-256

Poniższe hashe wiążą zarówno aktywne źródła wskazane w sekcji 3, jak i
zachowane kontrole historyczne. Sama obecność pliku w tym spisie nie czyni go
przodkiem aktywnego DAG-u; rolę logiczną określa mapa pokrycia.

### 6.1. Małe n i redukcja zakresu

~~~text
168e68b13a05bb93ffb43aa556e2ddfbc77235f6394c015a6bfe0f28069f8509  docs\erdos506_small_n_incidence_audit_2026-06-23.md
7ff8a6c25393a44a9e31a472a9f831d1f9b3726ee992351b661643945f778ae3  docs\erdos506_n6_survivor_geometry_2026-06-23.md
f9c49edf6ad68155745e663d8e805ac2cd6998538bce793c38fc7e082204e21d  docs\ERDOS506_N6_F9_ANALYTIC_PROOF_2026-08-04.md
d62415e66e71f5cbd5c183f3dbfc4d49676cab81bc30631d96a4e52609c68403  docs\ERDOS506_N7_F11_PROOF_2026-07-30.md
b88280003733d97e73ab70b52fa13d2d02a42c53f51eedfa8612d21abac06e15  reports\ERDOS506_N8_F17_CERTYFIKAT_2026-07-30_PL.md
40e022f9d8eacb0a39a0e059be6811351fd497671213a3f22571e1d846f55b8f  docs\ERDOS506_N8_F17_ANALYTIC_PROOF_2026-08-04.md
4de521abccfb4fa2bf5e1c59005512135e08804110d1fbe4a1bea73613af01a6  docs\ERDOS506_N9_LOCAL_CLOSURE_2026-07-30.md
b4eacbc826aafbb40c0925cb4ed2a983772843d6bf1878b1831aea478e10ed73  scratch\n9_analytic_closure_20260804\FULL_THEORETICAL_PROOF.md
3f0e55f121a15a09097bf7cf633750a27d3db9fa4055677a8a14f75587dc14c4  scratch\n9_analytic_closure_20260804\GAMMA4_ORCHARD_CLOSURE.md
67f337de873b7b896759bf8103b29a7f4ca3262648f520da99dc56b340e68825  scratch\n9_analytic_closure_20260804\GAMMA5_ANALYTIC_CLOSURE.md
90e6da0e2cfd6bbcb0c071935c5d72a920fe83c309e9d7523c49b115c7d356e6  scratch\n9_analytic_closure_20260804\REPORT.md
829d1c2ab5acc47862c51c48650874ef4cda315865121bc9b5b9650b8a114704  scratch\n9_analytic_closure_20260804\INDEPENDENT_REDTEAM.md
925c642237904dc72501a20b6adde4f8977eb2eb1148246cc0c93265b3aa2643  scratch\n9_analytic_closure_20260804\verify_symbolic.py
10c503d61d8c7ff91b038f5b12a8e82847c443f6b0dfa662186585f94a32e889  scratch\n9_analytic_closure_20260804\verify_concyclic_branch.py
ab03a37199d1d20d981990b57e1f8da86115efd78b5fad72b5e08e1b9fb84247  scratch\small_n4_n9_zero_bf_audit_20260804\REPORT.md
70f1040c62454d8d0fe911badbec4aac7fa8867824c5f20be92eea6ad0c394c2  docs\ERDOS506_N10_FINAL_EXACT_CLOSURE_2026-08-01.md
12b898b2d347101ad4d0dd1205394cdb0b7ad749d835e24be584e08fb0a1f3a5  scratch\n10_n11_low_hanging_analytic_20260804\REPORT.md
c405d641ab6b578e69dcfad3135ee1a9cfffe7deee7c51110f8f615f0684a7c2  scratch\n10_n11_low_hanging_analytic_20260804\N10_GAMMA4_FINAL_ANALYTIC_CLOSURE.md
37716cf86eea41e0122b1ee06b5f068db16fc732835830915240df2a5ffbc4c7  docs\ERDOS506_GAMMA6_X4_UNCONDITIONAL_BOUND_2026-07-30.md
e218accaa6f699885ca437fc8791bd977f86d20280f408d0b2f445e4f5fa6562  scratch\n10_gamma5_analytic_closure_20260804\C30_K4_LOCAL_THREE_CAP.md
f6318ae51413b35789414d05085b9e547b86f8c935580864515f5067b25098c2  scratch\n10_gamma5_analytic_closure_20260804\C30_K5_LOCAL_CUBE_CAP.md
93834c4e6e066f6bcb5e515699578c17be5c3f050c2d3fcc637339f40df0faba  scratch\n10_gamma5_analytic_closure_20260804\C31_ANALYTIC_CLOSURE.md
0b64a03b27337cfba3315ea701804675edc76367b7c99f74135f0b76b9602134  scratch\n10_gamma5_analytic_closure_20260804\C31_C32_LOW_K_CAPACITY_REDUCTION.md
a3f82eed5ba46fafac4926b129acb6ddb5cc4fa4b17cba2cc82bd0c0e8f1be8d  scratch\n10_gamma5_analytic_closure_20260804\C32_K2_DISJOINT_GOLDEN_LINK_CLOSURE.md
1769804952e503afe8e1d8bd3c497b39f9e6c463434ed96c1572f51dcb8cea12  scratch\n10_gamma5_analytic_closure_20260804\C32_K2_SATURATED_ANALYTIC_CLOSURE.md
39b5dc86a6919050e00a0ecc5c9e9aa8ffe3b937e6b0fa7e792adfe78ec2b6af  scratch\n10_gamma5_analytic_closure_20260804\C32_K3_RICHLINE_CLOSURE.md
fec8bdbd653b1e759c98f6a0014365b21207ce45ac83859f046fa9269ccb2f21  scratch\n10_gamma5_analytic_closure_20260804\K4_ALL_LOW_LOCAL_CAP.md
ba433ebcaa09ebac3a7e31366df8aff2a4e4a9c66a4864c126bfdf330abc7924  scratch\n10_gamma5_analytic_closure_20260804\K4_UNIVERSAL_ANALYTIC_CLOSURE.md
4988ab2c2b34960fab1af4b9d63ce068bcb90b32b9ee406cbef4fa9d29dea36a  scratch\n10_gamma5_analytic_closure_20260804\K6_QUADRIC_SIGN_CLOSURE.md
66b553301e1f9263e1818debe1feb088cfc66f836c5e19cc17e1f36641362123  scratch\n10_gamma5_analytic_closure_20260804\REPORT.md
01585c44139b3a6b79c19b55e33db3e5a5106b9dc4af2b7e7acee87720aac97c  scratch\n10_gamma5_analytic_closure_20260804\verify_symbolic.py
ae0a1917e7a6813836ae0325e5bf336171e5aff4baa67812eebd9aa72717a63e  scratch\n10_gamma5_analytic_closure_20260804\SIX_FIVEBLOCK_POWER_OBSTRUCTION.md
4a3577585aab8df77fe32056874fa7aa276bb620ae577cb0abf2351fc82ad7e1  docs\ERDOS506_FINITE_SMALL_CIRCLE_FARKAS_2026-07-30.md
5d000893f9435b76801e74c9278e2d6216c2e0ba1f4e26c504a260c90ef89ac0  docs\ERDOS506_COMPLETE_SOLUTION_ROADMAP_2026-08-02.md
~~~

### 6.2. Końcowe okno n=11,...,14

~~~text
3f4ea87cc1756354277b3e80e0d3705540c4fad3b2800254eec7a4a0cf4d8975  scratch\n11_full_closure_audit_20260804\REPORT.md
efb4f1edf46043aa4eadecbc94f796fbb5acb4fd67b586acf13c303c1ecb1fad  scratch\n11_zero_bruteforce_redteam_20260804\REPORT.md
0b8024e70c6e1c1e709607b8999e5260f0ba276400b7c47c119a15fc01d2802f  scratch\n11_gamma6_uniform_boundary_20260804\REPORT.md
ea19229376de3a26cfc17fc85015bc8eb8b465a846a46a8fac75d139096da68b  scratch\n11_gamma6_uniform_boundary_20260804\verify_exact.py
9c82efa8d4206ac904b34636be3f71ca001c6fecfeeab878882a4efbf72cb17a  scratch\n11_gamma6_uniform_boundary_20260804\FINAL_REDTEAM_AUDIT.md
c8ee6e02d18bacc763c87f4a1c44a29dd6e0b61c03040b54ef8f20b31dad154c  scratch\n11_zero_bruteforce_redteam_20260804\GAMMA6_UNIFORM_BOUNDARY_REDTEAM.md
d40387f283603479e0c021572be71bfc4382419d1a075a11d065931700996281  scratch\small_window_zero_bf_audit_20260804\REPORT.md
efa91de7c7c2f198cc4334537920f9609deec5632fcf5e4adf23470ab23e0151  scratch\n11_gamma5_c38_k8_short_reduction_redteam_20260804\REPORT.md
9659030edc66b91608784864ed9dc0713bdb84e84c7a090a8dfcec1655633827  scratch\n11_gamma5_c38_k8_short_reduction_redteam_20260804\verify_symbolic.py
286ca2a788dcc9be6ea344ca235c5d8e6eade8517eb01a16cc1bc7ef3a32e0e9  docs\ERDOS506_N12_GAMMA5_ANALYTIC_CLOSURE_2026-08-04.md
9928634b0f607d668acc05d3d89550c90fb77b268ff4957a1146958c70525ac3  scratch\added_center_melchior_transfer_20260804\STRONG_GAMMA5_TRANSFER.md
dc13286e9119882d577888e1117831de62fbdbddfa350b2e2da94c20f19cabc2  scratch\n12_gamma5_c48_obtuse_gram_closure_20260804\REPORT.md
30a95b40dd0541b07fb4988cf34bcb2986dbaaf4b9b25778d170a112193164ea  scratch\n12_gamma5_c48_obtuse_gram_closure_20260804\verify_exact.py
5900c833ee4905aebbb1dcc583baa53446d9d6302d7163af044ba10ed450d237  scratch\added_center_melchior_transfer_20260804\N12_GAMMA5_C48_C50_ANALYTIC_BRIDGE.md
72af4279918ac2732aca6e8d52f1f06e3f9b96410f820e422d45c66d9e1f44ed  scratch\n12_gamma5_fourway_inversion_geometry_20260804\REPORT.md
b2735f5b1fcb6c4b4602a5b94cdb6b24ed553d00e4be6eecabdf26382c2bb5e8  scratch\n12_gamma5_fourway_inversion_geometry_20260804\verify_exact.py
f2230245ce6bf936d45c7b19066ebcea12565f9ff103d9124f45a0d87d383e85  scratch\n12_gamma5_c49_defect_determinant_closure_20260804\REPORT.md
6df28726f4f9112654d97d025d53726774d416a74d406aa6e9e4f19968f30469  scratch\n12_gamma5_c49_defect_determinant_closure_20260804\verify_exact.py
a9f66eaae6a6281342e8c1f3e7f65b36aac0301a66f52f60c5dd546142467637  scratch\n12_c50_l14_fiveline_qz_closure_20260804\REPORT.md
e033c3bdabe3b2f7a1755ef5e494621931ebccd36e157e9544a38197d0fea4c1  scratch\n12_c50_l14_fiveline_qz_closure_20260804\verify_exact.py
4e57396a15cbfc5ddc1360a98a7f1889024f00ffa8276184a7f11593a64f2a5f  scratch\added_center_melchior_transfer_20260804\INDEPENDENT_C50_L14_ENDPOINT_UNION_AUDIT.md
b925c5453ef74735b6dd7d28c27b83faca5ce9a83d75c0f43b35a7c9e2983c35  scratch\added_center_melchior_transfer_20260804\N12_C50_KAPPA_PARITY_CLOSURE.md
5b7aac91314f6cb1796b869f810267c68016f929d77a711b64859f9eb89125d5  scratch\added_center_melchior_transfer_20260804\N12_C50_L14_H2K8_CLOSURE.md
06ed8ed264a44db982fb2dabfd436a062d7f5827d1f96672d73396ae402d2352  scratch\n12_c50_typeA_gallery_hall_obstruction_20260804\REPORT.md
efc6d69e4ecf5ca77382e0a810bc5dd0f673d184a205d3db3cfd150838c6348c  scratch\n12_c50_typeA_gallery_hall_obstruction_20260804\INDEPENDENT_TOPOLOGY_AND_TRANSFER_AUDIT.md
4693b8286b593859e4bf362f3fc7d67d3bec4d8f956c03c64bf820e12740cbc1  scratch\n12_c50_typeA_gallery_hall_obstruction_20260804\verify_symbolic.py
00bcc9be742e20d5dacda568021b164a650df5f4cd9d12c01d28b5c560ae44c7  scratch\n12_gamma5_fourway_global_dual_20260804\REPORT.md
4375a9636da42f640f7cdb700dbbd13d3a82877ee906333707f932507fb2f108  scratch\n12_gamma5_fourway_global_dual_20260804\global_dual_audit.py
a9e45a317c0bc7bc43c82ad422cb22118703ee8c2c8f6d215e506ed792c2dc00  scratch\four_agent_20260801\agent1_n12g6\REPORT.md
ba928e74376d834eab0b3c86591a6bb8768c21bfe4ab3c0489e33e3a715c3899  scratch\four_agent_20260801\agent1_n12g6\n12_gamma6_complete_closure_replay.py
3c01e7ae7ad7aff3b38776f675e830ce251082012fa81bfe01f71d3eab649569  scratch\four_agent_20260801\agent1_n12g6\n12_gamma6_complete_closure.json
3643ead2c55e590e4d661b329996e045b6ff19d65ec7646eae0502737cbf51d2  scratch\n12_gamma6_analytic_closure_20260804\REPORT.md
560f107202f6f0a25438e49b735ba51291f34b8428afc4f287aef027fed3077b  scratch\n12_gamma6_analytic_closure_20260804\verify_repaired_endpoint.py
e9cbd3215acd8fca34423828b47ff6f21b6a1aa8e319af04ca6de74b856f2b4b  scratch\n13_gamma5_added_center_global_closure_20260804\REPORT.md
8c581a9453e56f769331172c0df9c2b338e43b856613c90f8b897fc75fa729b7  scratch\n13_gamma5_added_center_global_closure_20260804\verify_symbolic.py
388a6dc34cf232f669480ed87f33f6118d16a01cf0d8e7d37226ba69f735888a  scratch\n13_gamma6_added_center_w47_cut_20260804\REPORT.md
65cce4301b01f3e458b1160a5199e6eeead1cb4d1550fc2cb35d9ec8d32d4170  scratch\n13_gamma6_w48_lattice_cut_20260804\REPORT.md
2fa88b479bfb403e0034b473752b1bfb1c2912663ff2e97556c81d1d0dd76bf7  scratch\n13_gamma6_w49_w51_lattice_host_cut_20260804\REPORT.md
1443d5d8ba76222b7c50f092e4b93116b8692d1549e76e86a5198d60352e6843  scratch\n13_gamma6_high_weight_event_capacity_closure_20260804\REPORT.md
95638d16051ecc32c17ab8e7d8bc7406c8ea60b7997e0ff299ab47b883ebe9d3  scratch\n13_gamma6_high_weight_event_capacity_closure_20260804\GEOMETRY_AND_CLOSURE_AUDIT.md
99fad9bb1def390bee8a38989f0227e3a2a4a9e7ffeeaa38638b8d060148e15f  scratch\n13_gamma6_high_weight_event_capacity_closure_20260804\verify_equations.py
59336ac1bf036d318dba6daaf48233d86c7e589f2450f18144b0291e5c259e98  scratch\n14_gamma6_added_center_global_dual_20260804\REPORT.md
eb88bb32c096c3ff21b64fde018bd53f1c3827b9a93fb022701e61ff5f9b8f9b  scratch\n14_gamma6_added_center_global_dual_20260804\verify_symbolic.py
~~~

### 6.3. Baza i indukcja n>=15

~~~text
f38ae68911b08bfb9ff9dccf2cc8fd6168eeebf8482a2edcbc18bbbe776d4340  scratch\n15_gamma5_gamma6_added_center_closure_20260804\REPORT.md
cd3cda5f3930c77ee2183bc826f6d4dc4daa864cccb6889757c261c86f0979f7  scratch\n15_gamma5_gamma6_added_center_closure_20260804\verify_symbolic.py
146c44ca7d2c7704e2477411080d9acc4c45e1acdaed7e70a5a9bf79d06af327  tests\test_erdos506_n15_gamma5_gamma6_added_center_closure.py
370773dd09def50604edcaa5a74b0b96f5d326dbdb50e297da55eca6c0015c1f  scratch\n15_gamma7_zero_bf_audit_20260804\REPORT.md
51c6557fc2fe1bbe64362b95d1ac7eb37c6ec3ff02dfd73a5709466e091dd1a3  scratch\n15_gamma7_zero_bf_audit_20260804\verify_symbolic.py
d1fe4a863cad309c3106d8b4495b174e25c0b0de1ed2139fde4778e2f7c309d2  scratch\n15_classification_free_closure_20260804\REPORT.md
6ff79b281f596a4b1a11ff40332999336d808cb3225f735cf625e45d071e2b08  scratch\n15_classification_free_closure_20260804\verify_exact.py
9928634b0f607d668acc05d3d89550c90fb77b268ff4957a1146958c70525ac3  scratch\added_center_melchior_transfer_20260804\STRONG_GAMMA5_TRANSFER.md
416c2ae5452abea779eb6c388b48574df772a1843bdcaf163e1409df1b8b8f64  scratch\agent_parametric_lemma\recover_n11_m6_forward_involution_cap_independent.md
47d8744ea10e5183fd5fddbf38eb043d14239802b4c0cdcbd7c5d5f6c98e9365  docs\ERDOS506_N14_N15_GAMMA7_SUPPORT_2026-07-31.md
5c6fac2bad976c3299a40fcfa80ff81b4a1a9985c07760a81bcbe42d88fc70d9  docs\ERDOS506_N16_DELETION_RAY_PACKING_2026-07-31.md
8aed5cdb6879618efac3e8ce61f7e0280becc35c4fc50e86e14dd3ccae5f9d78  erdos506_n16_deletion_ray_packing_audit.py
583758a30256f9388d7c97e0d95889b1b8bcdb30ac7e2540f353ec37848608c0  tests\test_erdos506_n16_deletion_ray_packing_audit.py
abd07da0ebe4c39248e9b22f5c15af294cb1a3d7c396b6c3cc6b6e04b0db8187  docs\ERDOS506_DELETION_LEMMA_N17_2026-07-30.md
~~~

### 6.4. Synteza, literatura i niezależne red-teamy

Raporty `SMALL_AND_INFINITE_DEPENDENCY_AUDIT` oraz
`CERTIFICATION_GAP_AUDIT` są snapshotami sprzed analitycznych domknięć
`n=9,10,11,12` i mostu bez klasyfikacji `PGL_2(R)`. Ich diagnozy starych
ścieżek pozostają historycznie użyteczne, lecz dawne werdykty zależności
zastępują raporty `small_n4_n9_zero_bf_audit`, `n11_zero_bruteforce_redteam`,
analityczny manifest `n=12`, `global_zero_bruteforce_audit` oraz
`n15_gamma7_zero_bf_audit`.

~~~text
4897df70eb797ee7b8466be627d4ca7bcfeec1c8754cca4c8ab51c4850ce1ed4  scratch\global_zero_bruteforce_audit_20260804\REPORT.md
454db15cd0475dc981bcd1cd471322dbbcc4c87c9fe15f0c593cfae22c52af3e  scratch\global_zero_bruteforce_audit_20260804\BRIDGE_SUPPLEMENT.md
f33bc8832a4f75ac3f91a2a5c7f91121638a734ad44f6c00618278360036b771  scratch\zero_bruteforce_coverage_20260804\MANIFEST.md
f8c53cc8790bf1eaaaedf588deda415c0b496b62088f94c5c75dd52c806929fe  docs\ERDOS506_V1_COMPLETE_PROOF_2026-08-04.md
c1d71003d294d97b560ec8e66cd1e7087275063e88f9646d4f653cfd387a96b3  docs\ERDOS506_LITERATURE_AND_PRIORITY_AUDIT_2026-08-04.md
e63d347202caefdaaccef20b7507484e7f6c1047659023d6819f3af3bffdfe99  scratch\final_paper_redteam_20260804\SMALL_AND_INFINITE_DEPENDENCY_AUDIT.md
bf5ef053c0e2f1e5e7cd857616831059e6839c1a0573f2aca420209e9e2edbb1  scratch\final_paper_redteam_20260804\FINITE_WINDOW_PROOF_SYNTHESIS.md
1e2b8c7bd8bac790378759d6c9dbbe51e58ccaf783b9529fc8781537dd138b5e  scratch\final_paper_redteam_20260804\CERTIFICATION_GAP_AUDIT.md
7d02f9c658f83d1500ca7a13cd1473de0d1e96d98689b4e8d7cd7e54e8fd84ec  scratch\final_paper_redteam_20260804\LATE_ANALYTIC_REVIEW_20260804.md
~~~

## 7. Granica certyfikacji

Status `CLOSED_LOCAL_LEDGER_V1__EXTERNAL_REVIEW_OPEN` nie powinien być
opisywany jako opublikowane, niezależnie potwierdzone ani pierwsze na świecie
rozwiązanie. Pozostają następujące zadania:

1. Aktywny DAG dla `n=4,...,15`, bazy `n=16` i kroku `n>=17` jest obecnie
   papierowy: nie używa SAT/ILP, katalogów supportów/orbit, enumeracji
   matchingów ani klasyfikacji skończonych podgrup. Historyczne DRUP/VIPR i
   replaye są niezależnymi kontrolami, nie ogniwami kompletności.
2. Checkery nowych gałęzi kontrolują arytmetykę, wyznaczniki i dominację
   współczynników. Nie zastępują zewnętrznej recenzji mostów geometrycznych;
   szczególnie nowe argumenty `n=11,Gamma6`, `n=12,Gamma5/Gamma6` i
   `n=15,Gamma7` powinny zostać sprawdzone przez niezależnych ekspertów.
3. Dowód importuje jawnie nazwane klasyczne twierdzenia incydencyjne, między
   innymi Melchiora, Kelly'ego--Mosera, Lenchnera i Langera. Nie importuje już
   BGS, Cuntza, Zhanga, Dumnickiego ani klasyfikacji `PGL_2(R)` do aktywnego
   korzenia.
4. Audyt literatury i pierwszeństwa nie znalazł konkurencyjnego rozwiązania,
   lecz brak znaleziska nie dowodzi pierwszeństwa. Teza musi pozostać
   oznaczona jako wariant V1 i zostać porównana słowo w słowo z kanoniczną
   treścią problemu 506 przed publicznym ogłoszeniem.
5. Wcześniejsza pełna regresja zakończyła się `744 passed, 1 skipped`.
   Regresja jest testem infrastruktury i historycznych kontroli, nie
   substytutem recenzji twierdzenia.

Są to zadania certyfikacyjne, redakcyjne i publikacyjne. W bieżącym lokalnym
ledgerze V1 nie pozostaje otwarta wartość n ani otwarta gałąź ekstremalna.
