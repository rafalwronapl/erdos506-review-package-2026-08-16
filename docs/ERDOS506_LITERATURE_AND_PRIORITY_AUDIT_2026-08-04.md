> **SUPERSEDED W CZĘŚCI `n=6` (2026-08-10).** Zapisana niżej wartość `9`
> jest fałszywa; `f_V1(6)=8`. Zobacz
> [ścisłą korektę](ERDOS506_N6_CORRECTION_2026-08-10.md). Pozostała treść
> pozostaje historycznym audytem literatury i pierwszeństwa.

# Erdős #506 — audyt literatury, wariantu i pierwszeństwa

Data sprawdzenia: 4 sierpnia 2026.

## 1. Najważniejszy wniosek

Lokalny wynik repo dotyczy dokładnie wariantu V1: punkty są różne, nie leżą
wszystkie na jednej prostej ani wszystkie na jednym okręgu, a liczone są
różne właściwe okręgi zawierające niewspółliniową trójkę wybranych punktów.

Publiczna strona problemu nadal opisuje małe `n` jako otwarte i zaznacza, że
oryginalne sformułowanie nie podaje jednoznacznie warunku zapobiegającego
degeneracji liniowej. Nie znaleziono zindeksowanej pracy ani preprintu z
wynikiem

```text
f_V1(4..8)=3,5,9,11,17,
f_V1(n)=1+binom(n-1,2)-floor((n-1)/2) dla n>=9.
```

To jest wynik audytu wyszukiwania, nie dowód pierwszeństwa. Przed publicznym
ogłoszeniem należy przesłać dokładną tezę i manuskrypt osobom prowadzącym
bazę Erdős Problems oraz specjalistom od geometrii kombinatorycznej.

## 2. Oryginalny problem i jego historyczna korekta

Oryginalne źródło Erdősa z 1961 roku pyta o minimalną liczbę okręgów
wyznaczanych przez `n` punktów nieleżących wszystkich na jednym okręgu, lecz
nie zapisuje warunku liniowego. Źródło:

P. Erdős, *Unsolved Problems*,
https://combinatorica.hu/~p_erdos/1961-22.pdf.

P. D. T. A. Elliott badał wersję, w której punkty nie leżą wszystkie na
jednej prostej ani na jednym okręgu:

P. D. T. A. Elliott, *On the number of circles determined by n points*,
Acta Mathematica Academiae Scientiarum Hungaricae 18 (1967), 181–188,
https://doi.org/10.1007/BF02020972.

Elliott podał dla dużego `n` granicę `binom(n-1,2)`. Purdy i Smith wskazali
pominięty składnik związany z parami antypodycznymi. Poprawiona wartość to

\[
1+\binom{n-1}{2}-\left\lfloor\frac{n-1}{2}\right\rfloor.
\]

Źródło:

G. B. Purdy, J. W. Smith, *Lines, Circles, Planes and Spheres*, Discrete &
Computational Geometry 44 (2011), 860–882,
https://arxiv.org/abs/0907.0724,
https://doi.org/10.1007/s00454-010-9270-3.

Publiczna karta problemu podaje tę samą historię, oznacza problem jako
„resolved up to a finite check” i nadal mówi, że małe `n` wydają się
otwarte:

T. F. Bloom, *Erdős Problem #506*,
https://www.erdosproblems.com/506.

Karta jest użytecznym aktualnym indeksem, ale w publikacji należy cytować
przede wszystkim Erdősa, Elliotta i Purdy’ego–Smitha.

## 3. Problem wszystkich okręgów a problem zwykłych okręgów

Należy bardzo wyraźnie oddzielić dwa zagadnienia.

W Erdős #506 liczymy wszystkie różne właściwe okręgi zawierające co najmniej
trzy punkty. Okrąg z czterema, pięcioma lub większą liczbą wybranych punktów
jest liczony raz.

W literaturze o ordinary circles liczy się okręgi zawierające dokładnie trzy
punkty. To bliski temat i część jego narzędzi jest użyteczna po inwersji,
ale jego twierdzenia nie rozwiązują automatycznie Erdős #506. Najważniejsze
współczesne źródło kontekstowe to:

A. Lin, M. Makhul, H. Nassajian Mojarrad, J. Schicho, K. Swanepoel,
F. de Zeeuw, *On sets defining few ordinary circles*,
https://arxiv.org/abs/1607.06597,
https://doi.org/10.1007/s00454-017-9885-8.

Praca dowodzi asymptotycznych twierdzeń strukturalnych dla zwykłych
okręgów. Nie zawiera znalezionego tu pełnego wykazu małych wartości V1.

## 4. Zewnętrzne twierdzenia używane w lokalnym dowodzie

### Melchior

Używana postać to

\[
t_2\ge3+\sum_{r\ge4}(r-3)t_r
\]

dla nietrywialnego rzeczywistego projektowego układu prostych. Jest to
konsekwencja wzoru Eulera i faktu, że każda komórka ma co najmniej trzy
boki. Oryginalne źródło:

E. Melchior, *Über Vielseite der projektiven Ebene*, Deutsche Mathematik 5
(1940), 461–475.

W finalnym manuskrypcie warto zamieścić krótki samodzielny dowód z formuły
Eulera, ponieważ eliminuje to zależność bibliograficzną w najczęściej
używanym lemacie.

### Kelly–Moser

Używana jest dolna granica liczby zwykłych prostych w rzeczywistym
niekolinearnym zbiorze punktów:

L. M. Kelly, W. O. J. Moser, *On the Number of Ordinary Lines Determined by
n Points*, Canadian Journal of Mathematics 10 (1958), 210–219,
https://doi.org/10.4153/CJM-1958-024-6.

### Langer

W kroku nieskończonym używana jest nierówność incydencyjna Langera w
postaci zebranej i objaśnionej przez de Zeeuwa:

F. de Zeeuw, *Spanned lines and Langer’s inequality*,
https://arxiv.org/abs/1802.08015.

Jej źródłem algebraiczno-geometrycznym jest:

A. Langer, *Logarithmic orbifold Euler numbers of surfaces with
applications*, Proceedings of the London Mathematical Society 86 (2003),
358–396, https://arxiv.org/abs/math/0012180,
https://doi.org/10.1112/S0024611502013874.

### Afiniczny wynik Lenchnera

Certyfikat `Gamma7` używa dolnej granicy liczby skończonych zwykłych punktów
w afinicznym układzie prostych. Właściwym źródłem dla formuły
`(2n-3)/7` jest:

J. Lenchner, *Improved Bounds for Euclidean Ordinary Points in Line
Arrangements*, Proceedings of CCCG 2007, Theorem 8,
https://cccg.ca/proceedings/2007/03a3.pdf.

Nie należy przypisywać tej mocniejszej formuły wcześniejszej wspólnej pracy
Lenchnera i Brönnimanna, która udowadnia słabszą granicę `n/6`.

### Historyczny import układów z punktami potrójnymi

Starsza wersja jednej warstwy `n=11` używała nieistnienia układu jedenastu
prostych z siedemnastoma punktami potrójnymi. Źródłem kontroli był:

M. Dumnicki, Ł. Farnik, A. Główka, M. Lampa-Baczyńska, G. Malara,
T. Szemberg, J. Szpond, H. Tutaj-Gasińska, *Line arrangements with the
maximal number of triple points*, https://arxiv.org/abs/1406.6662.

Import ten nie należy już do aktywnego DAG-u. Parzysty czterokrawędziowy
line-leave redukuje układ jedenastopunktowy do dziesięciu punktów z
trzynastoma trójprostymi; ich graf par zwyczajnych redukuje się z kolei do
zakazanego realnego linku `C6` udowodnionego samodzielnie w gałęzi
`n=10,Gamma<=4`.

## 5. Zależności usunięte z bazy `n=15`

Starszy lokalny ledger zamykał `n=15,Gamma5` i `n=15,Gamma6` przez
klasyfikację symplicjalnych układów czternastu prostych Cuntza. Nowy dowód
w `scratch/n15_gamma5_gamma6_added_center_closure_20260804/REPORT.md`
zastępuje oba użycia nierównością added-center i geometrią czterech
inwolucji sześciu punktów na konice.

Stary argument dla siedmiopunktowej prostej odwoływał się również do
twierdzenia o zwykłych okręgach, aby zamienić dolną granicę 84 na ścisłą.
Nowa tożsamość luzów

\[
C=84+D+R+E
\]

pokazuje bezpośrednio, że równość 84 wymusza wyłącznie okręgi
czteropunktowe. W gałęzi `Gamma5` albo `Gamma6` jest to niemożliwe.

Po przyjęciu nowego dowodu ani klasyfikacja Cuntza, ani to zaostrzenie
Zhanga nie są zależnością bazy `f_V1(15)=85` ani wynikającej z niej indukcji.
Mogą pozostać w historii projektu jako niezależne, starsze drogi.

Także gałąź `n=15,Gamma7` nie potrzebuje już klasyfikacji skończonych
podgrup `PGL_2(R)` ani replayu 76 matchingów. Porządek cykliczny sześciu
punktów koniki i normalna postać jednej macierzy rzędu sześć dają kap trzech
centrów na ustalonej prostej, a support jednej sygnatury jest matchingiem.
Zewnętrznym wejściem tej gałęzi pozostaje twierdzenie Lenchnera.

## 6. Audyt pierwszeństwa na dzień 4 sierpnia 2026

Przeszukano tytuł problemu, numer Erdős #506, dokładną formułę, wartości
`f(8)=17` i frazy dotyczące pełnego rozwiązania. Sprawdzono aktualną kartę
Erdős Problems, indeks arXiv oraz wyniki dla prac o okręgach wyznaczanych
przez punkty. Nie znaleziono konkurencyjnego preprintu ani publikacji
zawierających pełny wynik V1 dla wszystkich `n`.

Najmocniejsze bezpieczne sformułowanie brzmi więc:

```text
Według przeprowadzonego audytu literatury pełny wynik V1 nie występuje
w znalezionej literaturze ani w aktualnym statusie Erdős Problems.
```

Nie należy pisać „pierwsze rozwiązanie” bez odpowiedzi ekspertów i bez
sprawdzenia baz MathSciNet, zbMATH oraz cytowań Elliotta poza zwykłą
wyszukiwarką.

## 7. Kroki przed zgłoszeniem pracy

Lokalny ledger, analityczne zamknięcie `n=9`, wewnętrzne red-teamy oraz pełna
regresja są już zamrożone w hashowanym manifeście. Przed publicznym roszczeniem
o pierwszeństwo pozostają: przeredagowanie ledgera do jednego manuskryptu
publikacyjnego, sprawdzenie MathSciNet, zbMATH i pełnego drzewa cytowań
Elliotta oraz co najmniej dwie rzeczywiście zewnętrzne recenzje geometrii
`Gamma6`, bazy `n=15` i delecji. Następnie należy przesłać dokładną tezę i
tekst prowadzącym Erdős Problems oraz specjalistom od geometrii
kombinatorycznej.

W tytule i abstrakcie trzeba umieścić słowa „variant V1” albo pełne
założenie „not all collinear and not all concyclic”. Bez tego czytelnik może
błędnie odczytać wynik jako rozwiązanie wariantu bez trzech
współliniowych punktów.
