> **SUPERSEDED W CZĘŚCI `n=6` (2026-08-10).** Teza `f_V1(6)=9` i jej
> dowód są fałszywe; poprawna wartość to `8`. Zobacz
> [ścisłą korektę](ERDOS506_N6_CORRECTION_2026-08-10.md). Pozostała treść
> jest zachowana jako zamrożony zapis historyczny.

# Erdős #506 w wariancie V1 — pełny lokalny dowód i jego granica certyfikacyjna

Data: 4 sierpnia 2026.

## 1. Twierdzenie

Niech `P` będzie zbiorem `n` różnych punktów płaszczyzny rzeczywistej.
Zakładamy, że punkty nie leżą wszystkie na jednej prostej ani wszystkie na
jednym okręgu. Liczymy różne właściwe okręgi zawierające co najmniej trzy
niewspółliniowe punkty `P`; prostych nie liczymy jako okręgów. Niech
`f_V1(n)` oznacza najmniejszą możliwą liczbę takich okręgów.

Wtedy

\[
f_{V1}(4),\ldots,f_{V1}(8)=3,5,9,11,17,
\]

a dla każdego `n>=9`

\[
\boxed{
f_{V1}(n)=F(n):=
1+\binom{n-1}{2}-\left\lfloor\frac{n-1}{2}\right\rfloor .}
\tag{1.1}
\]

W szczególności

\[
f_{V1}(9),\ldots,f_{V1}(16)
=25,33,41,51,61,73,85,99.
\]

Jest to twierdzenie o wariancie V1. Nie wynika z niego automatycznie wariant,
w którym żadne trzy punkty nie mogą być współliniowe.

Status dokumentu jest następujący. Cały zakres jest domknięty w lokalnym
ledgerze matematycznym, a aktywny DAG dolnych granic nie potrzebuje
przeszukiwania konfiguracji, katalogów supportów, SAT/ILP ani klasyfikacji
orbit. Dawne replaye pozostają niezależnymi kontrolami historycznymi.
Checkery nowych gałęzi odtwarzają wyłącznie jawne tożsamości, współczynniki
i małe rachunki symboliczne; kompletność zapewniają argumenty zapisane w
tekście. Dowód nadal importuje nazwane klasyczne twierdzenia incydencyjne i
wymaga zewnętrznej recenzji matematycznej. Dokładną granicę certyfikacji
opisuje sekcja 16.

## 2. Konstrukcje osiągające podane liczby

Dla `n=4,5,6` oraz każdego `n>=9` bierzemy `n-1` punktów na okręgu `Gamma`
i jego środek `o`. Punkty na `Gamma` wybieramy w
`floor((n-1)/2)` parach antypodycznych, pozostawiając jeden punkt bez pary,
gdy `n-1` jest nieparzyste.

Wszystkie trójki punktów brzegowych wyznaczają `Gamma`. Trójka złożona z
`o` i pary antypodycznej jest współliniowa. Każda pozostała para punktów
brzegowych wraz z `o` wyznacza nowy okrąg. Okręgi odpowiadające dwóm różnym
parom są różne, ponieważ okrąg różny od `Gamma` przecina `Gamma` w najwyżej
dwóch punktach. Dostajemy więc dokładnie

\[
1+\binom{n-1}{2}-\left\lfloor\frac{n-1}{2}\right\rfloor=F(n)
\]

okręgów.

Dla `n=7` używamy wierzchołków trójkąta równobocznego, środków jego boków
i centroidu. Dokładny rachunek w `Q(sqrt(3))` daje sześć okręgów
czteropunktowych i pięć trzypunktowych, razem jedenaście.

Dla `n=8` używamy wymiernej konfiguracji zapisanej w
`artifacts/erdos-506-n8-f17`. Ma ona jedną prostą czteropunktową, dwie
proste trzypunktowe, jedenaście okręgów czteropunktowych i sześć okręgów
trzypunktowych. Wyznacza więc dokładnie siedemnaście właściwych okręgów.
Współliniowość i współokręgowość wszystkich podzbiorów sprawdzono
wyznacznikami nad liczbami wymiernymi.

Pozostała część tekstu dowodzi odpowiadających dolnych granic.

## 3. Język bloków

Maksymalnym blokiem uogólnionym nazywamy maksymalny podzbiór `P` o co
najmniej trzech punktach, leżący na jednej prostej albo na jednym właściwym
okręgu. Niech `L_s` oznacza liczbę maksymalnych `s`-prostych, `C_s` liczbę
maksymalnych właściwych `s`-okręgów, a

\[
B_s=L_s+C_s,\qquad C=\sum_{s\ge3}C_s.
\]

Każda trójka punktów ma dokładnie jednego właściciela: jeśli jest
współliniowa, jest zawarta w jednej maksymalnej prostej; w przeciwnym razie
wyznacza jeden okrąg i należy do jednego maksymalnego okręgu. Stąd podstawowa
tożsamość

\[
\sum_{s\ge3}\binom{s}{3}B_s=\binom n3.
\tag{3.1}
\]

Dwa różne właściwe okręgi mają co najwyżej dwa wspólne punkty. Dwie różne
proste mają co najwyżej jeden wspólny punkt, a prosta i właściwy okrąg — co
najwyżej dwa. Te proste fakty o przecięciach są źródłem wszystkich używanych
dalej packing bounds.

Dla punktu `p` niech `d_s(p)` będzie liczbą wszystkich maksymalnych
`s`-bloków przez `p`, a `l_s(p)` liczbą maksymalnych `s`-prostych przez `p`.
Po zsumowaniu po punktach mamy

\[
\sum_p d_s(p)=sB_s,\qquad
\sum_p l_s(p)=sL_s.
\tag{3.2}
\]

## 4. Inwersja, Melchior i dodany środek

Ustalmy `p in P` i odwróćmy pozostałe punkty przez inwersję o środku `p`.
Blok rozmiaru `s` przechodzący przez `p` staje się prostą zawierającą
`s-1` obrazów. Odwrócony zbiór nie jest współliniowy: współliniowość na
prostej przez środek oznaczałaby, że `P` było współliniowe, a współliniowość
na prostej nieprzechodzącej przez środek — że `P` było współokręgowe.

Nierówność Melchiora dla rzeczywistego układu punktów,

\[
t_2\ge3+\sum_{i\ge4}(i-3)t_i,
\tag{4.1}
\]

daje po inwersji punktowy luz

\[
\sigma_p:=d_3(p)-3-\sum_{s\ge5}(s-4)d_s(p)\ge0.
\tag{4.2}
\]

Po zsumowaniu:

\[
3B_3-\sum_{s\ge5}s(s-4)B_s\ge3n.
\tag{4.3}
\]

Druga postać tego samego mechanizmu jest mocniejsza dla bogatych prostych.
Po inwersji dodajemy z powrotem środek `o` jako punkt układu i ponownie
stosujemy Melchiora. Proste pierwotnej konfiguracji rozcinają pozostałe
punkty na rozłączne ramiona, więc

\[
l_2(p)+\sum_{s\ge3}(s-1)l_s(p)=n-1.
\tag{4.4}
\]

Po podstawieniu do (4.1) otrzymujemy lemat dodanego środka

\[
3l_3(p)+4l_4(p)+\sum_{s\ge5}s\,l_s(p)
\le n-1+\sigma_p.
\tag{4.5}
\]

Sumowanie i użycie (4.2) daje równoważną, wygodną postać globalną

\[
D:=\sum_{s\ge3}s(s-4)C_s
  +\sum_{s\ge3}2s(s-2)L_s
\le n(n-4).
\tag{4.6}
\]

Ujemny współczynnik `-3` przy zwykłym okręgu jest zamierzony. To właśnie
on pozwala łączyć nierówność z dokładnymi partycjami trójek.

## 5. Dwa lemata pękowe

### 5.1. Bogata prosta

Niech prosta `L` zawiera `m` punktów, a poza nią leży `k=n-m` punktów.
Każdy outsider i każda para punktów `L` wyznaczają właściwy okrąg. Dla
ustalonej pary outsiderów powtórzenia używają rozłącznych par punktów `L`:
gdyby dwie takie pary miały wspólny punkt, odpowiednie okręgi miałyby trzy
wspólne punkty, więc byłyby tym samym okręgiem, który zawierałby trzy
współliniowe punkty. Zatem

\[
C\ge k\binom m2-\binom k2\left\lfloor\frac m2\right\rfloor.
\tag{5.1}
\]

### 5.2. Bogaty okrąg

Niech właściwy okrąg `Gamma` zawiera `m` punktów, a poza nim leży `k`
punktów. Dla jednego outsidera co najwyżej `floor(m/2)` par punktów `Gamma`
jest z nim współliniowych. Dwa pęki outsiderów mają wspólnych co najwyżej
`floor(m/2)` okręgów, ponieważ wspólne okręgi zużywają rozłączne pary
punktów `Gamma`. Dwuwyrazowe włączenie–wyłączenie daje

\[
C\ge1+k\left(\binom m2-\left\lfloor\frac m2\right\rfloor\right)
-\binom k2\left\lfloor\frac m2\right\rfloor.
\tag{5.2}
\]

Oba lemata są słabsze od pełnego rachunku wielokrotnych przecięć, ale w
większości bogatych gałęzi mają duży zapas.

## 6. Wartości `n=4,5,6`

### 6.1. Cztery punkty

Jeżeli trzy punkty są współliniowe, czwarty wraz z każdą z trzech par na
tej prostej daje trzy różne okręgi. Jeżeli nie ma współliniowej trójki,
istnieją cztery niewspółliniowe trójki. Dwie z nich nie mogą należeć do
jednego okręgu, bo ich suma zawiera wszystkie cztery punkty, co przeczyłoby
założeniu V1. Zatem zawsze `C>=3`, a konstrukcja z sekcji 2 daje równość.

### 6.2. Pięć punktów

Prosta czteropunktowa i jeden outsider dają sześć różnych okręgów. Możemy
więc założyć, że wszystkie proste mają rozmiar co najwyżej trzy. Trójpunktowe
proste używają rozłącznych par, stąd jest ich najwyżej trzy.

Jeśli nie ma okręgu czteropunktowego, każda niewspółliniowa trójka daje
inny okrąg, a takich trójek jest co najmniej `10-3=7`. Jeśli istnieje
okrąg czteropunktowy `Gamma`, jest jedyny, bo dwa czteropunktowe podzbiory
pięciozbioru przecinają się w co najmniej trzech punktach. Każda
trójpunktowa prosta musi zawierać punkt spoza `Gamma` i dwa punkty `Gamma`.
Takie proste zużywają rozłączne pary na czterech punktach `Gamma`, jest ich
więc najwyżej dwie. Pozostaje co najmniej osiem niewspółliniowych trójek;
`Gamma` pokrywa cztery, a pozostałe cztery dają cztery dalsze okręgi.
Zawsze `C>=5`, a konstrukcja osiąga pięć.

### 6.3. Sześć punktów

Z (5.1) prosta cztero- lub pięciopunktowa daje co najmniej dziesięć
okręgów. Z (5.2) okrąg pięciopunktowy daje co najmniej dziewięć. Aby obalić
dolną granicę dziewięć, wystarczyłoby więc rozważyć układ, w którym każda
prosta ma rozmiar najwyżej trzy, a każdy właściwy okrąg najwyżej cztery.

Niech `L` będzie liczbą trójpunktowych prostych, `Q` liczbą
czteropunktowych okręgów, a `R` liczbą okręgów trzypunktowych. Mamy

\[
20=L+4Q+R,\qquad C=Q+R=20-L-3Q.
\tag{6.1}
\]

Ponieważ trójpunktowe proste zużywają po trzy rozłączne pary, `L<=5`.
Dwa różne czteropunktowe okręgi w sześciozbiorze muszą mieć dokładnie dwa
wspólne punkty; ich dwupunktowe dopełnienia są więc rozłączne. Stąd `Q<=3`.
Założenie `C<=8` w (6.1) wymusza `Q=3` i `L>=3`.

Każde trzy trójpunktowe proste na sześciu punktach, które parami mają co
najwyżej jeden punkt wspólny, tworzą układ boków trójkąta z jednym dodatkowym
punktem na każdym boku. Po afinicznej normalizacji można zapisać

\[
0=(0,0),\quad1=(1,0),\quad3=(0,1),
\]

\[
2=(a,0),\quad4=(0,b),\quad5=(s,1-s),
\]

gdzie `a,b,s` nie są zerem ani jedynką. Jedyną trójką
czteropunktowych okręgów zgodną kombinatorycznie z tym układem są bloki

\[
\{0,1,4,5\},\quad\{0,2,3,5\},\quad\{1,2,3,4\}.
\]

Ich równania współokręgowości redukują się do

\[
b+2s-1=0,\qquad a-2s+1=0,\qquad a-b=0.
\]

Wynika `s=1/2` i `a=b=0`, a więc zderzenie punktów. Nie mogą istnieć trzy
czteropunktowe okręgi. Sprzeczność dowodzi `C>=9`; konstrukcja z sekcji 2
ma dokładnie dziewięć.

## 7. Wartość `n=7`

Załóżmy `C<=10`. Z (5.1) prosta rozmiaru `4,5,6` daje odpowiednio co
najmniej `12,18,15` okręgów, więc wszystkie proste mają rozmiar najwyżej
trzy. Z (5.2) okrąg pięcio- lub sześciopunktowy daje odpowiednio co
najmniej `15,13`, więc każdy właściwy okrąg ma rozmiar najwyżej cztery.

Niech `L,Q,R` oznaczają liczby trójpunktowych prostych, czteropunktowych
okręgów i trzypunktowych okręgów. Wówczas

\[
35=L+4Q+R,\qquad C=35-L-3Q.
\tag{7.1}
\]

Twierdzenie Sylvestera–Gallaia pozostawia co najmniej jedną zwykłą prostą,
więc `3L<=20` i `L<=6`. Dopełnienia dwóch różnych czteropunktowych okręgów
są trójkami przecinającymi się w najwyżej jednym punkcie. Ich pary są więc
rozłączne, skąd `3Q<=21` i `Q<=7`. Nierówność `C<=10` w (7.1) daje
`L+3Q>=25`, a zatem `Q=7`.

Siedem trójek dopełniających zużywa wszystkie dwadzieścia jeden par
dokładnie raz. Tworzą one jedyny system Steinera `STS(7)`, czyli płaszczyznę
Fano. Podnosimy punkt `(x,y)` do

\[
(x,y,x^2+y^2,1)\in\mathbb R^4.
\]

Cztery punkty są zależne dokładnie wtedy, gdy pierwotne punkty są
współliniowe albo współokręgowe. Siedem wymuszonych zależności
czteroelementowych dawałoby rzeczywistą reprezentację matroidu Fano. Po
normalizacji bazy odpowiadające wyznaczniki dają

\[
ch=dg,\qquad bl=dj,\qquad el=hi,
\]

podczas gdy ostatni obwód wymaga

\[
-bgi-cej=0.
\]

Podstawienie redukuje lewą stronę do `-2begl/h`. Wszystkie dzielone
parametry są niezerowe, ponieważ odpowiadają niewymuszonym, niezależnym
czwórkom. Jest to niemożliwe nad liczbami rzeczywistymi; matroid Fano jest
reprezentowalny tylko w charakterystyce dwa. Stąd `C>=11`, a konstrukcja z
sekcji 2 kończy dowód.

## 8. Wartość `n=8`

Załóżmy `C<=16` i niech `m` będzie największą liczbą punktów na właściwym
okręgu. Lemat pękowy wyklucza `m=5,6,7`; wariant V1 wyklucza `m=8`.
Jeżeli `m=3`, liczba niewspółliniowych trójek jest co najmniej
`56-35=21`. Pozostaje `m=4`.

Bogata prosta rozmiaru co najmniej pięć daje z (5.1) więcej niż szesnaście
okręgów. Wszystkie maksymalne bloki mają więc rozmiar trzy albo cztery.
Połóżmy

\[
b=B_4=C_4+L_4,\quad L=L_3+L_4,\quad h=L_4.
\]

Z partycji trójek, sumowanego Melchiora, Melchiora dla pierwotnych prostych
i lematu dodanego środka otrzymujemy kolejno

\[
B_3+4b=56,
\tag{8.1}
\]

\[
K:=\sum_p(d_3(p)-3)=144-12b\ge0,
\tag{8.2}
\]

\[
3L+4h\le25,
\tag{8.3}
\]

\[
9L+7h\le200-12b,
\tag{8.4}
\]

oraz

\[
C=56-3b-L.
\tag{8.5}
\]

Z `C<=16` i (8.3)–(8.5) wynika `b in {11,12}`.

Dla `b=11` mamy `K=12`, a równania wymuszają `L=7,h=0`. Lokalny luz po
dodaniu środka,

\[
\kappa_p=7+(d_3(p)-3)-3l_3(p),
\]

jest dodatnią liczbą całkowitą przystającą do jedynki modulo trzy. Suma
ośmiu takich luzów wynosi jednak

\[
56+12-9\cdot7=5,
\]

co jest niemożliwe.

Dla `b=12` wszystkie luzy `d_3(p)-3` znikają i

\[
\kappa_p=7-3l_3(p)-4l_4(p)\ge0.
\tag{8.6}
\]

Po dualizacji układu ośmiu prostych komórki można dwukolorować znakiem
iloczynu ośmiu form liniowych. Każda krawędź układu sąsiaduje z jedną
komórką każdego koloru, więc suma długości brzegów w każdej klasie jest
równa liczbie krawędzi `E`. Nadmiar nad trójkątami w klasie `i` ma zatem
postać `E-3F_i`; oba nadmiary są przystające modulo trzy. Ich nieujemna suma
nie może być równa jeden, więc `kappa_p` nie może być równe jeden. Z (8.6) wynika
`l_3(p)<=1`. Sumowanie i (8.3)–(8.5) zostawia wyłącznie

\[
L_3=2,\qquad L_4=2,\qquad C=16.
\tag{8.7}
\]

Suma luzów wynosi wtedy sześć. Lokalne możliwości wymuszają, że dwie
czteroproste są rozłączne i dzielą osiem punktów na dwie czwórki, a każda
z dwóch trójprostych składa się z punktów należących do tych czwórek.
W dowolnej trójce dwa punkty należą do tej samej czwórki, więc jej prosta
pokrywałaby się z odpowiednią czteroprostą. Sprzeczność. Zatem `C>=17`, a
wymierna konstrukcja daje równość.

## 9. Wartość `n=9`: dowód analityczny

Konstrukcja z ośmioma punktami na okręgu i jego środkiem daje

\[
1+\binom{8}{2}-4=25.
\]

Dla dolnej granicy zakładamy `C<=24` i rozdzielamy przypadki według liczby
`m` punktów na największym właściwym okręgu `Gamma`. Dla outsidera `x`
co najwyżej `floor(m/2)` cięciw `Gamma` przechodzi przez `x`, a dla ustalonej
pary outsiderów ich wspólne okręgi używają rozłącznych par punktów `Gamma`.
Nierówność Bonferroniego daje więc

\[
C\ge 1+(9-m)\left(\binom m2-\left\lfloor\frac m2\right\rfloor\right)
-\binom{9-m}{2}\left\lfloor\frac m2\right\rfloor .
\tag{9.1}
\]

Dla `m=8,7,6` prawa strona wynosi odpowiednio `25,34,28`.

Jeżeli `m=3`, każda niewspółliniowa trójka wyznacza własny okrąg. Niech
największa prosta ma `r` punktów. Trójka współliniowa, która nie leży na tej
prostej, zawiera z niej co najwyżej jeden punkt, a każda para pozostałych
punktów może dobrać najwyżej jeden punkt tej prostej. Liczba trójek
współliniowych jest zatem nie większa niż

\[
\binom r3+\binom{9-r}{3}+\binom{9-r}{2}\le56,
\]

więc `C>=84-56=28`.

Rozważmy `m=4`. Najpierw ten sam rachunek pęków dla prostej zawierającej
`r=5,6,7,8` punktów daje `28,36,39,28`, więc żadna prosta nie ma więcej niż
cztery punkty. Niech `B` oznacza liczbę czteropunktowych uogólnionych
okręgów, czyli właściwych okręgów i prostych, a `L=l_3+l_4` liczbę bogatych
prostych. Partycja 84 trójek i Melchior dają

\[
C=84-3B-L,\qquad 3l_3+7l_4\le33,
\]

stąd `L<=11`. Założenie `C<=24` wymusza `B>=17`.

Odwróćmy konfigurację względem dowolnego wybranego punktu. Pozostałych osiem
punktów jest niewspółliniowych i żadne cztery nie leżą na prostej. Każdy
czteroblok przechodzący przez pivot staje się prostą trzypunktową. Dla ośmiu
rzeczywistych punktów bez czwórki współliniowej takich prostych jest najwyżej
siedem. Krótki dowód tej wersji lematu Orcharda jest zawarty w pakiecie
`n9_analytic_closure_20260804`: ewentualne osiem prostych wymusza jedyny
abstrakcyjny układ Möbiusa--Kantora `8_3`, a jego ostatnia incydencja po
normalizacji projektowej daje `u^2-u+1=0`, niemożliwe nad liczbami
rzeczywistymi. Sumując po dziewięciu pivotach, otrzymujemy

\[
4B\le9\cdot7,
\]

czyli `B<=15`, sprzecznie z `B>=17`.

Pozostaje `m=5`. Piszemy `P=Gamma\sqcup X`, gdzie `|X|=4`, oraz

\[
R=\sum_t t\,l_{2,t}.
\]

Jest to liczba incydencji outsiderów z prostymi będącymi cięciwami
`Gamma`; matching na pięciu punktach daje `R<=8`. Niech `S_x` będzie
rodziną okręgów przez `x` i dwa punkty `Gamma`. Wtedy

\[
\sum_x|S_x|=40-R,
\]

a dla pary outsiderów `|S_x\cap S_y|<=2`. Ponieważ okrąg typu `(2,4)`
miałby sześć punktów, potrójna poprawka inkluzji--ekskluzji kończy się na
typie `(2,3)`. Z `C<=24` wynika kluczowa nierówność

\[
R\ge5+c_{2,3}+c_{\le1}.                           \tag{9.2}
\]

Cztery punkty `X` mają dokładnie jedną z czterech postaci. W położeniu
ogólnym ich cztery trójki dają cztery różne okręgi liczone po prawej stronie
(9.2), więc `R>=9`. Gdy wszystkie cztery są współliniowe, oznaczając przez
`a=c_{1,2}` i `b=c_{2,2}`, dostajemy `a+2b=30` oraz `b<=12`; dokładny bilans
daje wtedy `C=26-R+3a/2>=27`.

Gdy dokładnie trzy punkty `X` są współliniowe, równość we wszystkich
ograniczeniach wymusza, że każda para outsiderów jest podwójnie obsadzona
przez rozłączne pary z `Gamma`. Bilans pozostałych trójek i Melchior dają
ponadto, że trzy okręgi outsiderowych trójek wyczerpują
`c_{2,3}+c_{\le1}`, a więc `c_{1,2}=0`. Następnie bilans właścicieli daje
`l_{1,2}=0` oraz `a+s=2`, gdzie `s` mówi, czy trójprosta zawiera punkt
`Gamma`. Dwie różne trójki czteroelementowego zbioru pokrywają jednak tylko
pięć z sześciu par outsiderów, więc szósta trójka nie ma właściciela.

W ostatnim przypadku cztery punkty `X` leżą na okręgu `Omega`. Lemat osi
potęgowej liczy bloki `2+2` poprzez przecięcia cięciw na osi potęgowej
`Gamma,Omega`. Daje najwyżej 12 bloków dla układu `5+4` oraz najwyżej 10 dla
`4+4`; równość 12 w drugim układzie wymagałaby współliniowości trzech
punktów diagonalnych pełnego czworokąta, których znormalizowany wyznacznik
wynosi `-2`. Po zapisaniu `b=12-e`, `v=l_{2,2}`, `a=c_{1,2}` otrzymujemy

\[
R\ge6+e+a,\qquad e+a\le2,\qquad
\ell+2v=6-a+2e-6\delta,
\]

gdzie `delta` oznacza wspólny punkt `Gamma` i `Omega`. Dla `delta=0` kap
`b+v<=12` daje `v<=e`, podczas gdy Melchior wymaga `5v>=3+9e`. Dla
`delta=1` kap `b+v<=10` wymusza `e=2,a=v=0,R=8`, a wtedy `\ell=4` i lewa
strona Melchiora wynosi `36>33`. Oba przypadki są niemożliwe.

Wszystkie wartości `m=3,...,8` są więc wykluczone i wynik brzmi

\[
f_{V1}(9)=25.
\tag{9.3}
\]

Pełne wyprowadzenie lematu Orcharda, wszystkich czterech konfiguracji
outsiderów i naprawionego przypadku pokrywających się cięciw znajduje się w
`scratch/n9_analytic_closure_20260804/`. Starszy pakiet CP-SAT/MILP pozostaje
niezależną kontrolą historyczną, ale nie jest już aktywnym ogniwem dowodu.

## 10. Wartość `n=10`

Konstrukcja daje trzydzieści trzy okręgi. Pod `C<=32` wszystkie gałęzie mają
obecnie ścieżki bezkatalogowe. Największy okrąg rozmiaru co najmniej siedem
zamyka rachunek pęków. `Gamma6` zamykają nierówność `U17` i dokładny dual
Farkasa. Potrzebne w `U17` kapy sygnatur wynikają elementarnie z porządku
cyklicznego sześciu punktów koniki: możliwe są tylko `R3,S1,S3,S5`, a jawna
normalna postać ich czterech centrów pokazuje, że na ustalonej prostej leżą
najwyżej trzy. Nie jest potrzebna klasyfikacja skończonych podgrup
`PGL_2(R)`.

Dla największego okręgu rozmiaru co najwyżej cztery globalne tożsamości
redukują kontrprzykład do jednego profilu

\[
(B_3,B_4;L_3,L_4,L_5)=(20,25;13,0,0).
\]

Samodzielny ośmiopunktowy lemat Orcharda dowodzi, że każdy dziewięciopunktowy
link ma graf zwykłych par `C_3\sqcup C_3`: alternatywę `C_6` odrzucają dwa
krótkie argumenty współrzędnościowe nad liczbami rzeczywistymi. Sklejenie
linków dzieli następnie dwadzieścia trójbloków na pięć granic tetraedrów,
więc `L_3<=5`, sprzecznie z `L_3=13`. Wartości tabelaryczne BGS ani katalog
orbit linków nie są aktywnymi wejściami tej gałęzi.

Całą gałąź `Gamma5` zamyka teraz jeden argument strukturalny. Piszemy
`x=B_3`, `b=B_4`, `k=B_5` i `a=#{p:d_3(p)=9}`. Partycja trójek, inwersja w
punkcie, Kelly--Moser i parzystość komórek dają

\[
x+4b+10k=120,\qquad x=20+a,\qquad d_3(p)\in\{6,9\},
\]

oraz punktowy luz `kappa(p)>=0`, `kappa(p)≠1`. Sześć pięciobloków wyklucza
obstrukcja potęgowa, pięć — lokalny argument sześcianu, a cztery — kompletny
argument wektorowo-incydencyjny kończący się rzeczywistą sprzecznością
`3s^2+1=0`. W dwóch ostatnich warstwach pozostaje zatem `B_5<=3`.

Punktowe pojemności zamykają `C<=30`. Przy `C=31` równania zostawiają tylko
`(k,a,L)=(2,0,11),(3,2,11)` i oba wiersze przegrywają z wymaganą liczbą
incydencji trójprostych. Przy `C=32` pięć wierszy agregatowych redukuje się
do dokładnie czterech podprzypadków

\[
(B_5,a,h)=(2,0,0),\qquad (3,2,1),(3,2,2),(3,2,3).
\]

Trzy wiersze `B_5=3` usuwa pełna analiza topologii czteroprostych; jedyny
przypadek równości dawałby w linku dziewięciopunktowym matching rozmiaru
cztery tam, gdzie graf `C_3\sqcup C_3` ma matching rozmiaru dwa. Dla `B_5=2`
przecięcie bloków daje ten sam zabroniony link, a przypadek rozłączny
nasyca oś potęgową. Dwie kompletne near-one-factorizations prowadzą do

\[
a=1-b,\quad b^2+b-1=0,\quad ap=b-1,\quad 2ap=b,
\]

więc `b=2`, sprzecznie z równaniem kwadratowym. Argument jest zapisany w
`scratch/n10_gamma5_analytic_closure_20260804/REPORT.md` i plikach, do
których raport odsyła. Używa wartości `f_{V1}(9)=25` w kroku delecji; dzięki
analitycznemu dowodowi z sekcji 9 nie przenosi już zależności od CP-SAT ani
MILP. Nie potrzebuje katalogu profili, SAT, ILP, DRUP ani VIPR. Starsze
pakiety 1461 profili, DRUP i VIPR pozostają niezależną ścieżką kontrolną, a
nie aktywną koniecznością dowodu `Gamma5`.

Zatem

\[
f_{V1}(10)=33.
\tag{10.1}
\]

## 11. Redukcja skończonego okna `n=11,...,15`

Redukcja jest sekwencyjna. Zakładamy, że wartość dla `n-1` została już
udowodniona, i rozważamy kontrprzykład spełniający `C<=F(n)-1`. Usunięcie
punktu `p` daje

\[
C(P)=C(P-p)+o_P(p),
\]

gdzie `o_P(p)` liczy właściwe okręgi zawierające dokładnie trzy punkty
konfiguracji, w tym `p`. Po uwzględnieniu dwóch zdegenerowanych możliwości
dla `P-p` — wszystkich punktów na jednej prostej albo na jednym okręgu —
otrzymujemy

\[
o_P(p)\le F(n)-F(n-1)-1.
\tag{11.1}
\]

Jeżeli maksymalna prosta lub maksymalny właściwy okrąg ma `m` punktów, pęk
przez outsidera daje przeciwną dolną granicę na `o_P(p)`. Dokładne rozbicie
czterech klas resztowych prowadzi do kapu

\[
m\le M_n=\left\lfloor\frac n2\right\rfloor+2.
\tag{11.2}
\]

To nie jest założenie certyfikatów małych okręgów, lecz ich wcześniejsza
hipoteza wyprowadzona z indukcyjnie znanej wartości. Pełny rachunek, w tym
przypadki zdegenerowane po usunięciu punktu, zapisano w
`docs/ERDOS506_DELETION_LEMMA_ATTACK_2026-07-30.md` i odtwarza go
`erdos506_deletion_lemma_rich_block_audit.py`.

W każdym przypadku wybieramy największy właściwy okrąg `Gamma_m`. Małe
wartości `m` zamykają dokładne wymierne kombinacje Farkasa tożsamości
trójkowej (3.1), sumowanego Melchiora (4.3), Kelly’ego–Mosera i globalnej
nierówności dla prostych. Bogate wartości `m` zamykają (5.2) lub
wzmocnione, rozdzielone rachunki pęków. Po tych redukcjach trzeba rozważyć
następujące gałęzie centralne:

\[
\begin{array}{c|c}
n& m\\ \hline
11&5,6\\
12&5,6\\
13&5,6\\
14&5,6,7\\
15&5,6,7.
\end{array}
\tag{11.3}
\]

W szczególności gałęzie `Gamma4` dla `n=11,12` nie zamykają się samym
optymalnym wynikiem ciągłego LP. Dla `n=11` dual daje `C>=118/3`, po czym
przy `C<=40` całkowitość zostawia `C=40`, a równanie resztowe wymusza
niecałkowite `L_6=3/2`. Dla `n=12` dual daje `C>=4565/92`; jedyny możliwy
endpoint `C=50` wymagałby nieujemnych liczb całkowitych spełniających

\[
29a+63m+40p=105,
\]

co jest niemożliwe. Dopiero te dwa kroki całkowitościowe kończą `Gamma4`.

Każdy wiersz w (11.3) ma obecnie aktywną ścieżkę papierową. Gałęzie
`Gamma5` zamykają kombinacje added-centre, lokalne luzy i obstrukcje
incydencyjne; gałęzie `Gamma6` — duale wagowe, kapy sygnatur i krótkie
argumenty całkowitościowe. Dla `(14,7)` i `(15,7)` jawne funkcjonały
Farkasa opierają się tylko na wyświetlonych nierównościach skalarnych oraz
lematach geometrycznych. Historyczne katalogi i replaye pozostają kontrolą,
lecz nie są przodkami żadnego z końcowych wniosków.

## 12. Wartości `n=11` i `n=12`

### 12.1. Jedenaście punktów

Zakładamy `C<=40`. Gałęzie `m<=4` i `m>=7` zamykają odpowiednio partycja
trójek z dualem Farkasa i (5.2). Dla `Gamma6` footprint ma jedną z trzech
postaci `(10,0,0),(6,1,0),(0,0,1)`. Dwa jawne funkcjonały Farkasa i jedno
zaokrąglenie Chvátala--Gomory'ego wykluczają `C<=38`. Dla `C=39,40`
pełne pary outsiderów mają najwyżej cztery sygnatury; zakaz powtórzenia na
sąsiednich krawędziach, unikalny czterohost i kap trzech centrów na śladzie
hosta dają w footprintcie B granicę `W<=26`. Przy `C=39` funkcjonał wymaga
`W>=27`; przy `C=40` równość `W=26` zeruje wszystkie luzy i wymusza pięć
różnych pełnych centrów liniowych, choć globalny kap wynosi cztery.

W footprintcie C budżet `C=39` daje `sigma_{17}+l_{22}=1`, a ciasny wiersz
szósty redukuje to do niemożliwej równości `12l_{05}=6`. Przy `C=40` typ
`l_{15}` przekracza cały budżet; trzy pozostałe typy hosta dają kolejno
`22<=W<=20`, `28<=W<=26` oraz `14<=J<=13`. Wyczerpuje to `Gamma6` bez
dawnych katalogów 17 i 103 profili; footprint A jest prostszy, bo już
funkcjonał F1 daje w nim `C>=41`.

Pozostaje `Gamma5`. Dla punktu `p` wybranego pięciokręgu niech `a_p` liczy
właściwe zwykłe okręgi przez `p`. Lenchner po inwersji daje `a_p>=3`, zatem
`sum_{p\in Gamma}a_p>=15`. Delecja pozostawia dziesięciopunktowy zbiór V1,
więc `C-a_p>=f_{V1}(10)=33`; po zsumowaniu
`5C-sum_{p\in Gamma}a_p>=165`. Dodanie obu nierówności daje `C>=36`, czyli
zakres `C<=35` jest pusty bez katalogu typów. Warstwy `C=36,37` usuwa bezpośrednio połączenie
delecji, kongruencji stopni i punktowego lematu dodanego środka. Przy
`C=38` równania zostawiają cztery wartości `B_5=k=5,6,7,8`. Trzy pierwsze
odrzuca wypukły rachunek krańcowego kosztu lokalnego luzu i moment przecięć
pięciobloków. Dla `k=8` wybór jednego pięciokręgu daje tożsamość

\[
A_{04}=-R-3A_{05},
\]

więc `R=A_{05}=A_{04}=0`; obstrukcja trzech niewspółliniowych centrów
diagonalnych pełnego czworokąta prowadzi następnie do sprzeczności `0=5`.
Nie występuje tu lista supportów ani orbit.

Warstwy `C=39,40` mają już argumenty analityczne. Dla `C=39` globalna
redukcja daje

\[
L\in\{12,15\},\qquad 0\le H\le30,
\]

wyklucza `H<=25` i `H=30`, a cykliczny separator usuwa kolejno
`H=26,27,28,29`. Dla `C=40` tożsamości dają dokładniej

\[
L\equiv2\pmod3,\qquad L\le17,\qquad
25L+3N_5\ge254,\qquad N_5\le8.
\]

Nierówności usuwają `L=8`. Przy `L=17` wszystkie siedemnaście prostych są
trójproste, a cztery pary zwyczajne tworzą graf o samych parzystych
stopniach, więc `C_4`. Usunięcie jego wierzchołka daje dziesięć punktów bez
czwórki współliniowej i trzynaście trójprostych.

Taki układ dziesięciopunktowy także jest niemożliwy elementarnie. Partycja
par daje sześć par zwyczajnych. Jeśli `r_p,s_p` są stopniami trójprostych i
par zwyczajnych w punkcie, to `9=2r_p+s_p` oraz `sum s_p=12`; graf zwyczajny
ma więc postać `K_{1,3}\sqcup3K_2`. Po usunięciu wierzchołka stopnia trzy
pozostaje dziewięciopunktowy link z dziesięcioma trójprostymi i grafem
zwyczajnym `C_6\sqcup3K_1`. Sekcja 3 samodzielnego dowodu
`N10_GAMMA4_FINAL_ANALYTIC_CLOSURE.md` odrzuca dokładnie taki realny link.
Ten sam lemat dziesięciopunktowy uzasadnia krok lokalny używany później w
`L=14`: gdyby `d_3=6,d_5=0`, równanie par dawałoby `d_4=13`, a po inwersji
otrzymalibyśmy właśnie zabronione trzynaście trójprostych bez czwórki
współliniowej. Sprzeczność usuwa `L=17` i oba dawne importy Dumnickiego bez
zewnętrznej klasyfikacji. Pozostają dokładnie
`L=11,14`. Warstwa `L=11` zamyka się dla wszystkich
`N_5=5,6,7,8`. Dla `L=14` Melchior pozostawia rozłączny podział

\[
L_5=1,L_4=0;\quad
L_5=0,L_4=0;\quad
L_5=0,L_4\in\{1,2\}.
\]

Pierwszy przypadek zamyka redukcja bogatej prostej. Drugi — argument
Kelly’ego–Mosera dla samych trójprostych. W trzecim lemat dodanego środka

\[
7L_4+16L_5\le N_5+2
\]

oraz końcowe cięcia przecięć wykluczają wszystkie `N_5`. Wyczerpuje to
`C<=40`, zatem

\[
f_{V1}(11)=41.
\tag{12.1}
\]

### 12.2. Dwanaście punktów, `Gamma6`

Gałąź `Gamma6,C<=50` ma domknięcie analityczne, które nie używa katalogu
footprintów ani replayu jako wyroczni kompletności. Wycentrowane wektory incydencji dają
`1<=B_6<=4`, `B_5<=12` oraz wspólną nierówność Grama dla pięcio- i
sześciobloków. Kolejne sekcje wykluczają `B_6=4`, `B_6=3`, wszystkie warstwy
`B_6=2` i wreszcie `B_6=1`. Szczególnie delikatny endpoint
`B_6=2,s=2,B_5=6` ma `d_5=(3^{10},0^2)`. Sześć pięciobloków dzieli się na
dwie klasy po trzy; ich pary dają dokładnie sześć współincydencji na ośmiu
punktach nośnych, podczas gdy każdy punkt nośny wymusza co najmniej jedną,
czyli łącznie co najmniej osiem. Sprzeczność zamyka endpoint bez błędnego
argumentu o minimalizacji momentu. Pełny, po red-teamie poprawiony dowód jest
w `scratch/n12_gamma6_analytic_closure_20260804/REPORT.md`. Historyczny
replay 3221 footprintów pozostaje wyłącznie niezależną kontrolą.

### 12.3. Dwanaście punktów, `Gamma5`

Eliminacja współczynnikowa (13.1)--(13.4) pokrywa `C<=44`. Dla
`C=45,46,47` stosujemy mocny transfer z sekcji 13. Warstwa `C=48` odpada
przez układ wektorów rozwartokątnych i ograniczenie rzędu macierzy Grama.
Warstwa `C=49` ma dwa niezależne dowody: inwersję z parzystością oraz
determinant defektu. Żaden z tych kroków nie enumeruje supportów.

Przy `C=50` globalny most wymusza

\[
B_6=0,\qquad K=B_5,\qquad L=14.
\]

Jeżeli istnieje pięcioprosta, dla każdego punktu `p` oznaczamy przez
`z_p=l_5(p)` jego incydencję z pięcioprostą, a przez `q_p` przesunięty lokalny
slack zwykłej-prostej. Lokalne ograniczenie ma postać `q_p>=-z_p`, podczas
gdy dokładne sumy dają `sum z_p=5` oraz `sum q_p=3-k<=-7`. Przeczy to
`sum q_p>=-5`, więc `L_5=0`. Dla `L_5=0` globalne
sumy redukują problem do sześciu punktów końcowych

\[
(L_4,B_5)=(0,8),(0,9),(0,10),(1,8),(1,9),(2,8).
\tag{12.3}
\]

Parzystość i obstrukcja sum sześciogwiazdowych usuwają cztery z nich.
Punkt `(2,8)` wymusza profil stopni `(4^4,3^8)` i dwie różne czteroproste
o tym samym nośniku, co jest niemożliwe. Dla `(0,8)` dokładne momenty
nie wystarczają same: dopiero po dołożeniu Kelly’ego–Mosera oraz parzystości
komórkowej `kappa!=1` zostają dokładnie trzy profile punktowe. Każdy zawiera
lokalny typ A. Po inwersji
i dodaniu środka typ A dawałby układ dwunastu prostych z

\[
(t_2,t_3,t_4)=(6,14,3)
\]

i wyróżnioną prostą sygnatury `3D+4T`. Sztywność galerii sprowadza układ do
sześciu wymuszonych trójek, a jawny siedmiokrawędziowy transversal łamie
warunek Halla. Zatem `C=50` także nie istnieje.

Łącznie

\[
f_{V1}(12)=51.
\tag{12.4}
\]

## 13. Mocny transfer dla `Gamma5`

Ta sekcja daje wspólny analityczny rdzeń dla `n=12,13,14,15`. Po
wykluczeniu prostych rozmiaru co najmniej siedem wszystkie bloki mają
rozmiary `3,4,5,6`, przy czym sześciobloki są prostymi. Połóżmy

\[
T=\binom n3,
\]

\[
P=3B_3-5B_5-12B_6=3n+K,\qquad K\ge0,
\]

\[
S=3L_3+4L_4+10L_5+12L_6,
\]

\[
A=5L_3+12L_4+20L_5+28L_6.
\]

Z (3.1), (4.3) i (4.6) dostajemy

\[
A\le4C+n(n-4)-T+C_5,
\tag{13.1}
\]

\[
A\ge\frac53S.
\tag{13.2}
\]

Kluczowe połączenie jest współczynnikowe i zachodzi blok po bloku:

\[
24T+27P\le35(S+3C).
\tag{13.3}
\]

Dla bloków rozmiaru `3,4,5,6` współczynniki lewej strony wynoszą
`105,96,105,156`; po prawej każdy właściwy okrąg ma współczynnik 105, a
proste odpowiednio `105,140,350,420`. Ponadto

\[
12B_4+35B_5+72B_6=3T-P\le3T-3n.
\tag{13.4}
\]

Dla `n=14` równania (13.1)–(13.4) dają

\[
470-5C\le A\le4C-194,
\]

więc `C>=74`. To zamyka `Gamma5` silniej niż wymagana granica 73.

Dla `n=13` pierwsze połączenie daje `C>=59`. Dokładna analiza końców
`C=59,60` redukuje liczbę bloków do

\[
(B_3,B_4,B_5,B_6)=(48+2K,7-3K,21+K,0),
\quad K\in\{0,1,2\}.
\]

Punktowa partycja par ma postać

\[
7d_5(p)+3d_4(p)=63-\sigma_p.
\]

Dla `K=0` cztery punkty musiałyby leżeć na wszystkich siedmiu
czteroblokach. Dla `K=1` suma stopni pięciobloków wyniosłaby 116 zamiast
110. Dla `K=2` punkt dodatniego luzu wymagałby więcej niż jednego
czterobloku, choć globalnie istnieje tylko jeden. Zatem `C>=61`.

Dla `n=12` te same równania wykluczają `C=45`, a przy `C=46,47` zostawiają
odpowiednio `L=15` i `L=14`. Punktowa wersja (4.5) daje

\[
\sum_p r_p\le36+K,
\]

podczas gdy liczba incydencji punkt–bogata prosta wynosi co najmniej `3L`.
Otrzymujemy odpowiednio `45<=41` i `42<=41`, sprzeczność.

Dla `n=15`, gdzie `T=455` i `P>=45`, z (13.3)

\[
S+3C\ge\frac{2427}{7}.
\]

Z (13.4) mamy `C_5<=B_5<=37`, więc (13.1)–(13.2) dają

\[
\frac{4045}{7}-5C\le A\le4C-253.
\]

Stąd

\[
C\ge\frac{5816}{63}>92,
\tag{13.5}
\]

co w szczególności wyklucza `C<=84`.

## 14. Wartości `n=13,14,15`

### 14.1. Trzynaście punktów, `Gamma6`

Niech `Gamma` będzie sześciopunktowym okręgiem, a `X` siedmiopunktowym
dopełnieniem. Dla okręgu różnego od `Gamma`, zawierającego dwa punkty
`Gamma` i `x` outsiderów, wprowadzamy wagę

\[
W=\sum_x\binom{x}{2}c(2,x).
\]

Added-center dual najpierw wymusza `W>=48`. Jego wejściami są cztery
partycje trójek

\[
(T_0,T_1,T_2,T_3)=(35,126,105,20),
\]

punktowy dolny limit zwykłych okręgów, pivot Melchior na `X` oraz
`D<=117`. Współczynnikowa nierówność po zsumowaniu ma postać

\[
123D\ge141T_0+340T_1+539T_2+141T_3
-414W+79O+199M_X-1344C.
\]

Dla `W<=46` przeczy ona `D<=117`; endpoint `W=47` wymusza zerowanie
wszystkich luzów, po czym równanie `M_X=240-123f=21` ma niecałkowite
rozwiązanie.

Drugi dual i kongruencja kratowa usuwają `W=48`. Krótkie przedziały dla
współrzędnej `delta=7m-4j` usuwają `W=49` i `W=51`; przy `W=50` zostaje
jedna wartość agregatowa, lecz wymaga dwóch różnych okręgów zawierających
po pięć z siedmiu outsiderów. Ich footprinty przecinają się w co najmniej
trzech punktach, więc okręgi musiałyby być równe.

Każda z 21 par outsiderów ma wagę najwyżej trzy. Niech `F` oznacza liczbę
par pełnych, czyli par o wadze trzy. Mamy

\[
W\le2\binom{7}{2}+F.
\]

Pełna para outsiderów odpowiada jednej z najwyżej czterech inwolucji bez
punktów stałych sześciu zaznaczonych punktów na konice. Support jednej
sygnatury jest matchingiem na `X`, więc ma najwyżej trzy krawędzie. Zatem
`F<=12` i `W<=54`; zakres `W>54` jest niemożliwy.

Pozostaje `W=52,53,54`. Liczba zdarzeń
powtórzenia sygnatury jest co najmniej `2r`, gdzie `r=W-48`. Każde takie
zdarzenie ma unikalny blok-gospodarza. Dokładna nierówność pojemności daje

\[
R_{rep}\le E,\qquad4E\le6r+7+8A,
\]

gdzie `A=c(0,6)` liczy sześciopunktowe bloki outsiderów. Nie wolno usunąć
składnika `8A` samą arytmetyką. Dla `r=4` taki blok wyklucza budżet. Dla
`r=5,6` musiałby on jednocześnie gościć powtórzenia wszystkich czterech
pełnych sygnatur, lecz centra czterech odpowiadających inwolucji nie mogą
leżeć na jednej ustalonej prostej gospodarza. Stąd osobno `A=0`. Dopiero
wtedy, z `R_rep>=2r`, wynika `8r<=6r+7`, niemożliwe dla `r=4,5,6`.
Gałąź jest zamknięta i razem z sekcją 13 daje

\[
f_{V1}(13)=61.
\tag{14.1}
\]

### 14.2. Czternaście punktów, `Gamma6`

Teraz `|X|=8`. Oznaczmy przez `P_i` liczbę trójek z dokładnie `i` punktami
na `Gamma`. Mamy

\[
(P_0,P_1,P_2,P_3)=(56,168,120,20).
\]

Niech `W` będzie sumą `binom(x,2)` po niewybranych okręgach zawierających
dwa punkty `Gamma` i `x` outsiderów. Pivot Melchior daje

\[
M_\Gamma\ge18,\qquad M_X\ge24,
\]

a lemat dodanego środka `D<=140`. Dla każdego bloku zachodzi
współczynnikowa nierówność, której suma daje

\[
4D\ge6P_0+9P_1+12P_2+6P_3
+3M_\Gamma+6M_X-36C-6W.
\tag{14.2}
\]

Pod `C<=72` prawa strona i `4D<=560` wymuszają `W>=76`.

Dla pary outsiderów okręgi przez tę parę i dwa punkty `Gamma` używają
matchingu na sześciu punktach, więc są najwyżej trzy. Jeśli są trzy,
powstaje pełna sygnatura: inwolucja bez punktów stałych sześciu punktów
na konice. Projektywność rzeczywistej koniki zachowuje albo odwraca porządek
cykliczny, dlatego jej działanie na sześciu zaznaczonych punktach zanurza
się w `D_6`. Są najwyżej cztery takie inwolucje. Jedna sygnatura nie może
wystąpić na dwóch sąsiednich parach outsiderów, więc jej support jest
matchingiem w `K_8` i ma najwyżej cztery krawędzie. Co najwyżej szesnaście
z dwudziestu ośmiu par jest pełnych, a zatem

\[
W\le16\cdot3+12\cdot2=72.
\]

Sprzeczność `76<=W<=72` zamyka gałąź. Sekcja 13 zamyka `Gamma5`, a dokładny
certyfikat zamyka `Gamma7`; pozostałe rozmiary usuwają redukcje z sekcji 11.
Stąd

\[
f_{V1}(14)=73.
\tag{14.3}
\]

### 14.3. Piętnaście punktów bez klasyfikacji Cuntza

Zakładamy `C<=84`. Najpierw trzeba starannie potraktować siedmiopunktową
prostą, dla której surowa nierówność (5.1) daje tylko równość 84.

Niech `L` będzie siedmiopunktową prostą, a `X` ośmioma outsiderami. Dla
okręgu `Omega` z unii pęków oznaczmy przez `j(Omega)` liczbę jego punktów w
`X`. Wtedy

\[
\sum_\Omega j(\Omega)=8\binom{7}{2}=168,
\]

\[
\sum_\Omega\binom{j(\Omega)}2\le\binom{8}{2}\,3=84.
\]

Jeśli `D` oznacza defekt drugiej nierówności, `R` sumę
`\binom{j-1}{2}`, a `E` liczbę okręgów spoza unii pęków, to tożsamość
`1=j-\binom{j}{2}+\binom{j-1}{2}` daje dokładnie

\[
C=84+D+R+E.
\tag{14.4}
\]

Równość wymusza, że wszystkie właściwe okręgi są czteropunktowe. Przeczy
to istnieniu wybranego pięcio- albo sześciopunktowego okręgu. Proste
rozmiaru co najmniej osiem mają w (5.1) wynik ściśle większy od 84. W
gałęziach `Gamma5` i `Gamma6` każda prosta ma więc rozmiar najwyżej sześć.

Gałąź `Gamma5` zamyka (13.5): używa kapu bloków rozmiaru sześć oraz
wynikającego z `12B_4+35B_5+72B_6<=1320` ograniczenia `C_5<=37`. Checker
nowego raportu kontroluje końcową arytmetykę; pełne współczynniki źródłowe
transferu `Gamma5` pozostają związane z jego osobnym raportem, a nie są
wszystkie ponownie wyprowadzane przez ten checker. Dla `Gamma6` mamy
dziewięciu outsiderów i

\[
(P_0,P_1,P_2,P_3)=(84,216,135,20),
\]

\[
M_\Gamma\ge18,\qquad M_X\ge27,
\qquad D\le165.
\]

Ta sama nierówność (14.2) daje pod `C<=84`

\[
4D\ge1380-6W.
\]

Ponieważ `4D<=660`, otrzymujemy `W>=120`.

Na dziewięciu outsiderach są trzydzieści sześć par. Nadal istnieją najwyżej
cztery pełne sygnatury, a support każdej jest matchingiem rozmiaru najwyżej
cztery. Liczba pełnych par jest więc najwyżej szesnaście i

\[
W\le3\cdot16+2(36-16)=88.
\]

Sprzeczność `120<=W<=88` zamyka `Gamma6`. Checker sprawdza tu każdy
dopuszczalny typ blokowy. Przejścia geometryczne — matching przy parze
outsiderów, słownik secanta–centrum–inwolucja, zakaz sąsiednich wystąpień
sygnatury i brak rzeczywistej prostej na użytej kwadryce — są natomiast
dowodami tekstowymi, niezależnie zredteamowanymi, a nie proof-objectem.

Gałąź `Gamma7` ma dokładny wymierny certyfikat Farkasa dający

\[
C\ge\frac{37166}{441}>84.
\]

Wśród jego wejść są twierdzenie Lenchnera dające po cztery właściwe zwykłe
okręgi na pivot oraz nierówność `W+6N_{1,6}<=84`. Tę drugą otrzymujemy bez
przeglądu 76 matchingów. Dla bogatego hosta `(1,6)` pełna krawędź nie może
używać punktu `Gamma` leżącego na hoście, bo dwa właściwe okręgi dzieliłyby
wtedy niewspółliniową trójkę. Sygnatura jest więc doskonałym matchingiem na
pozostałym `Gamma6`, a jej centrum leży na przecięciu płaszczyzn liftu
`Gamma` i hosta. Pełne krawędzie używają zatem co najwyżej trzech sygnatur
o centrach na jednej ustalonej prostej, a support każdej sygnatury jest
matchingiem rozmiaru najwyżej trzy. Co najmniej sześć z piętnastu krawędzi
ma więc defekt jeden. Ponadto dwa różne footprinty sześciopunktowe w ośmiu
outsiderach przecinają się w co najmniej czterech punktach, więc dwa różne
hosty `(1,6)` byłyby tym samym okręgiem; stąd `N_{1,6}<=1`. Dostajemy
potrzebną nierówność.

Kap trzech centrów nie wymaga klasyfikacji skończonych podgrup
`PGL_2(R)`. Porządek cykliczny sześciu punktów koniki zostawia tylko
`R3,S1,S3,S5`; jeżeli istnieją wszystkie cztery, normalna postać jednej
macierzy rzędu sześć daje jawnie cztery centra, z których dokładnie trzy są
współliniowe. Nowy checker odtwarza 34 współczynniki funkcjonału oraz tę
normalną postać, nie generując matchingów ani supportów.

`Gamma<=4` zamyka certyfikat małych okręgów granicą `C>=290/3>84`.
Dla `Gamma=m>=8` bezpośredni rachunek pęków daje dla `m=8,...,14` kolejno

```text
85, 133, 151, 171, 163, 139, 85.
```

W konsekwencji

\[
f_{V1}(15)=85.
\tag{14.5}
\]

Ważna zmiana względem starszego ledgera: dowód (14.4), transfer (13.5),
sprzeczność wagowa dla `Gamma6` i powyższy argument `Gamma7` usuwają z bazy
`n=15` klasyfikację Cuntza, twierdzenie Zhanga, klasyfikację skończonych
podgrup `PGL_2(R)` oraz replay 76 matchingów. Pozostaje jawnie nazwane
klasyczne wejście Lenchnera.

## 15. Punkt `n=16` i indukcja

### 15.1. Szesnaście punktów

Niech

\[
\Delta_{16}=F(16)-F(15)=14.
\]

Załóżmy, że konfiguracja szesnastopunktowa ma `C<=98` i że każdy punkt
leży na najwyżej trzynastu zwykłych okręgach. Dla punktu `p` każda
trójpunktowa prosta przez `p` zużywa rozłączną parę spośród pozostałych
piętnastu punktów, zatem `l_3(p)<=7`. Po zsumowaniu

\[
3L_3\le16\cdot7=112.
\tag{15.1}
\]

Założenie o zwykłych okręgach i lemat pękowy ograniczają każdy blok do
rozmiaru dziewięć. Dla każdego możliwego największego okręgu
`m=3,...,9` rozdzielamy bloki według liczby punktów na `Gamma_m` i poza
nim. Dokładne wymierne kombinacje partycji trójek, (15.1), Melchiora,
Langera, nierówności par prostych oraz matchingów na konice dają dolne
granice większe od 98. Najsłabszy przypadek to `m=6`:

\[
C\ge\frac{20041}{204}=98+\frac{49}{204}>98.
\]

Sprzeczność dowodzi, że istnieje punkt na co najmniej czternastu zwykłych
okręgach. Po jego usunięciu pozostaje konfiguracja V1; w przeciwnym razie
osobny lemat krytycznej delecji daje bezpośrednio wymaganą liczbę okręgów.
Używając `f_V1(15)=85`, otrzymujemy

\[
C(P)\ge85+14=99=F(16).
\]

Konstrukcja daje równość.

### 15.2. Krok dla każdego `n>=17`

Niech

\[
\Delta_n=F(n)-F(n-1).
\]

Zakładamy przeciwnie, że `C(P)<F(n)` i każdy punkt leży na najwyżej
`Delta_n-1` zwykłych okręgach. Lemat bogatego bloku ogranicza wszystkie
linie i okręgi do

\[
M=\left\lfloor\frac n2\right\rfloor+2.
\]

Oprócz partycji trójek (3.1) i sumowanego Melchiora (4.3) stosujemy
sumowaną nierówność Langera

\[
\sum_{s=3}^M s(s-1)B_s
\ge\frac{n(n-1)(n+2)}3
\tag{15.2}
\]

oraz Melchiora dla pierwotnych prostych

\[
\sum_{s=3}^M
\left(\binom s2+\max(0,s-3)\right)L_s
\le\binom n2-3.
\tag{15.3}
\]

Kładziemy

\[
\alpha=\frac1{2M},\quad
\beta=\frac{M+1}{6M},\quad
\gamma=\frac{M-2}{12M},\quad
\delta=\frac13
\]

i bierzemy kombinację

\[
\alpha(3.1)+\beta(4.3)+\gamma(15.2)-\delta(15.3).
\]

Współczynnik okręgu rozmiaru trzy lub cztery wynosi jeden. Dla
`5<=s<=M` jego defekt do jedynki jest równy

\[
\frac{(M-s)(s-4)(s-3)}{12M}\ge0.
\]

Współczynnik trójprostej wynosi zero, czteroprostej `-4/3`, a dla prostej
rozmiaru `s>=5` jest równy

\[
\frac{(s-3)(-3Ms-4M+s^2-4s)}{12M}\le0.
\]

Współczynnik każdej prostej jest więc niedodatni. Zatem kombinacja jest nie
większa od `C(P)` i daje

\[
B(n)=
\frac1{2M}\binom n3
+\frac{M+1}{6M}\,3n
+\frac{M-2}{12M}\frac{n(n-1)(n+2)}3
-\frac13\left(\binom n2-3\right).
\tag{15.4}
\]

Dla `n=2r`

\[
B(n)-F(n)=
\frac{(r-2)(2r^3-13r^2-36r+18)}{9(r+2)}\ge0
\quad(r\ge9),
\]

a dla `n=2r+1`

\[
B(n)-F(n)=
\frac{4r^4-28r^3-45r^2+120r+27}{18(r+2)}\ge0
\quad(r\ge8).
\]

To przeczy `C(P)<F(n)`. Istnieje więc punkt `p` na co najmniej `Delta_n`
zwykłych okręgach. Przed zastosowaniem indukcji trzeba sprawdzić, że `P-p`
nadal spełnia V1. Gdyby `P-p` leżał na jednym okręgu, pęk outsidera `p`
dawałby już

\[
1+\binom{n-1}{2}-\left\lfloor\frac{n-1}{2}\right\rfloor=F(n)
\]

właściwych okręgów; gdyby leżał na jednej prostej, dostalibyśmy granicę
jeszcze silniejszą. Obie możliwości przeczą `C(P)<F(n)`. Zatem `P-p` jest
konfiguracją V1, wolno zastosować hipotezę indukcyjną i dodać znikające
zwykłe okręgi:

\[
C(P)\ge F(n-1)+\Delta_n=F(n).
\]

Baza `n=16` kończy indukcję dla całego nieskończonego zakresu.

## 16. Co dokładnie jest dowodem komputerowo wspomaganym

Dowód nie powinien ukrywać komputerowych ogniw pod słowem „sprawdzenie”.
Ich role są różne. Rozróżniamy trzy poziomy: replay rachunkowy sprawdzający
tożsamości i współczynniki; niezależny proof-object dla skończonego modelu,
na przykład DRUP albo VIPR; oraz dowód matematyczny sprawdzany przez
recenzenta, czasem z jawnym twierdzeniem zewnętrznym. Przejście testu z
pierwszej kategorii nie zastępuje dwóch pozostałych.

W aktywnym DAG-u tego tekstu komputer nie przeszukuje konfiguracji. Przy
`n=8` kontroluje jedynie wymierną konstrukcję i rachunki, a dolna granica
jest analityczna. Przy `n=9` dawne CP-SAT/MILP i katalogi orbit są wyłącznie
historyczną kontrolą. Dla `n=10` trzy centralne gałęzie mają odpowiednio:
samodzielny Orchard-link i sklejenie tetraedrów, strukturalny dowód
`Gamma5` oraz `U17` z cyklicznym kapem sygnatur. BGS, DRUP/VIPR i
klasyfikacja `PGL_2(R)` nie są potrzebne aktywnej ścieżce.

Przy `n=11` warstwy `Gamma5,C=36,37,38,39,40` oraz całe `Gamma6,C<=40`
mają argumenty papierowe. W szczególności nowy dowód `Gamma6,C=39,40`
zastępuje katalogi 17/103 profili jednym argumentem footprintowym. Przy
`n=12` całe `Gamma5,C<=50` zamyka sześć jawnych endpointów skalarnych i
obstrukcje Grama/parzystości/Halla, a całe `Gamma6` — niezależny dowód
incydencyjny dla `1<=B_6<=4`. Dawne replaye obu wartości pozostają tylko
kontrolami.

Gałęzie `n=13,14` są bezkatalogowe. Redukcje kratowe dla
`(13,Gamma6)` są krótkimi dowodami kongruencyjnymi, nie enumeracją
supportów. Dla `n=15` transfer `Gamma5`, sprzeczność wagowa `Gamma6` i nowy
34-typowy funkcjonał `Gamma7` usuwają Cuntza, Zhanga, 76 matchingów oraz
klasyfikację skończonych podgrup `PGL_2(R)`. Punkt `n=16` używa siedmiu
jawnych funkcjonałów na typach `(kind,g,x)`, a krok `n>=17` jednego
symbolicznego funkcjonału zależnego od `M`.

Checkery odtwarzają arytmetykę, wyznaczniki i dominację współczynników; nie
zastępują tekstowych mostów geometrycznych. Zewnętrznymi wejściami pozostają
jawnie nazwane klasyczne twierdzenia, między innymi Melchiora,
Kelly'ego--Mosera, Lenchnera i Langera. Pełna regresja repozytorium jest
testem infrastruktury, nie certyfikacją twierdzenia.

Pełny lokalny wynik jest zatem mocniejszy niż sam eksperyment obliczeniowy,
ale słabszy pod względem zewnętrznej certyfikacji niż jednolity dowód
sformalizowany w asystencie dowodów.

## 17. Mapa plików dowodowych

Główny hash-bound ledger znajduje się w
`docs/ERDOS506_V1_FINAL_LOCAL_MANIFEST_2026-08-04.md`.

Małe wartości opisują:

```text
docs/ERDOS506_N7_F11_PROOF_2026-07-30.md
docs/ERDOS506_N8_F17_ANALYTIC_PROOF_2026-08-04.md
docs/ERDOS506_N9_LOCAL_CLOSURE_2026-07-30.md
scratch/n9_analytic_closure_20260804/FULL_THEORETICAL_PROOF.md
scratch/n9_analytic_closure_20260804/GAMMA4_ORCHARD_CLOSURE.md
scratch/n9_analytic_closure_20260804/GAMMA5_ANALYTIC_CLOSURE.md
scratch/n9_analytic_closure_20260804/INDEPENDENT_REDTEAM.md
scratch/n9_analytic_closure_20260804/verify_symbolic.py
docs/ERDOS506_N10_FINAL_EXACT_CLOSURE_2026-08-01.md
scratch/n10_n11_low_hanging_analytic_20260804/N10_GAMMA4_FINAL_ANALYTIC_CLOSURE.md
scratch/n10_gamma5_analytic_closure_20260804/REPORT.md
scratch/global_zero_bruteforce_audit_20260804/BRIDGE_SUPPLEMENT.md
```

Pełny audyt `n=11` i zamknięcia `n=12` są w:

```text
scratch/n11_full_closure_audit_20260804/REPORT.md
scratch/n10_n11_low_hanging_analytic_20260804/REPORT.md
scratch/n11_zero_bruteforce_redteam_20260804/REPORT.md
scratch/n11_gamma6_uniform_boundary_20260804/REPORT.md
scratch/n11_gamma6_uniform_boundary_20260804/FINAL_REDTEAM_AUDIT.md
docs/ERDOS506_N12_GAMMA5_ANALYTIC_CLOSURE_2026-08-04.md
scratch/n12_gamma6_analytic_closure_20260804/REPORT.md
```

Analityczne transfery końcowego okna są w:

```text
scratch/added_center_melchior_transfer_20260804/STRONG_GAMMA5_TRANSFER.md
scratch/n13_gamma6_added_center_w47_cut_20260804/REPORT.md
scratch/n13_gamma6_w48_lattice_cut_20260804/REPORT.md
scratch/n13_gamma6_w49_w51_lattice_host_cut_20260804/REPORT.md
scratch/n13_gamma6_high_weight_event_capacity_closure_20260804/REPORT.md
scratch/n14_gamma6_added_center_global_dual_20260804/REPORT.md
scratch/n15_gamma5_gamma6_added_center_closure_20260804/REPORT.md
scratch/n15_gamma7_zero_bf_audit_20260804/REPORT.md
scratch/global_zero_bruteforce_audit_20260804/REPORT.md
scratch/global_zero_bruteforce_audit_20260804/BRIDGE_SUPPLEMENT.md
```

Zakres nieskończony opisują:

```text
docs/ERDOS506_N16_DELETION_RAY_PACKING_2026-07-31.md
docs/ERDOS506_DELETION_LEMMA_N17_2026-07-30.md
```

## 18. Wniosek

Konstrukcje z sekcji 2 dają wszystkie potrzebne górne granice. Sekcje
6–10 dają dokładne wartości dla `n=4,...,10`. Sekcje 11–14 zamykają
skończone okno `n=11,...,15`. Każda z tych dolnych granic ma aktywny DAG
bez przeszukiwania konfiguracji i klasyfikacji orbit. Sekcja 15 daje bazę
`n=16` i indukcję dla każdego `n>=17`. Otrzymujemy twierdzenie z sekcji 1
w całym naturalnym zakresie `n>=4` dla wariantu V1. Status ten oznacza
kompletny lokalny dowód oczekujący na niezależną recenzję, nie ogłoszone
ani zweryfikowane zewnętrznie pierwszeństwo.
