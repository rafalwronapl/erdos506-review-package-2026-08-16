# Erdős #506, wariant V3: pełne rozwiązanie lokalne

Data: 4 sierpnia 2026.

## 1. Wariant i wynik

Przez `V3` rozumiemy następujący, mocniejszy wariant zadania. Mamy `n`
różnych punktów płaszczyzny rzeczywistej, żadne trzy nie są współliniowe,
a cały zbiór nie leży na jednym okręgu. Liczymy różne właściwe okręgi
euklidesowe wyznaczone przez trójki wybranych punktów. Prostych nie liczymy.

Niech `f_V3(n)` oznacza najmniejszą możliwą liczbę takich okręgów.

**Twierdzenie.** Dla każdego całkowitego `n>=4`

\[
\boxed{
f_{V3}(n)=
\begin{cases}
20,&n=8,\\[2mm]
1+\binom{n-1}{2},&n\ne8.
\end{cases}}
\]

W szczególności

\[
(f_{V3}(4),\ldots,f_{V3}(10))=(4,7,11,16,20,29,37).
\]

Dowód dla wszystkich `n>=11` jest jednolity. Nie korzysta z przeszukiwania
konfiguracji, SAT, ILP ani klasyfikacji skończonych przypadków. Wyjątkowa
wartość dla `n=8` pochodzi z jawnej konfiguracji wymiernej.

## 2. Konstrukcje górne

Oznaczmy

\[
G(n)=1+\binom{n-1}{2}.
\]

Dla dowolnego `n` wybieramy `n-1` punktów na okręgu `Gamma`, a następnie
punkt `x` poza `Gamma` i poza wszystkimi prostymi przechodzącymi przez dwie
wybrane wcześniej pozycje. Takiego `x` można wybrać, bo zakazanych prostych
jest skończenie wiele. Żadne trzy punkty nie są wtedy współliniowe.

Wszystkie trójki leżą albo w `Gamma`, albo składają się z `x` i pary punktów
`Gamma`. Pierwszy rodzaj daje jeden okrąg, drugi dokładnie
\(\binom{n-1}{2}\) różnych okręgów. Dwa okręgi drugiego rodzaju nie mogą się
pokryć: wspólny okrąg zawierałby co najmniej trzy punkty `Gamma`, a więc
musiałby być równy `Gamma`, choć zawiera `x`. Otrzymujemy

\[
f_{V3}(n)\le G(n).                                      \tag{2.1}
\]

Dla `n=8` istnieje lepsza konfiguracja. Ponumerujmy punkty od `0` do `7`:

\[
\begin{aligned}
p_0&=(1/2,3/2),&p_1&=(-1/2,3/2),\\
p_2&=(1/10,17/10),&p_3&=(-1/10,17/10),\\
p_4&=(1/5,7/5),&p_5&=(-1/5,7/5),\\
p_6&=(1/13,21/13),&p_7&=(-1/13,21/13).
\end{aligned}                                           \tag{2.2}
\]

Jest to obraz dwóch współśrodkowych kwadratów o wierzchołkach
\((\pm1,\pm1)\) i \((\pm1/2,\pm1/2)\) przez inwersję o środku `(0,2)` i promieniu
`1`. To wyjaśnia symetrię konstrukcji, ale jej weryfikacja nie wymaga
rachunku przybliżonego ani własności rysunku.

Dokładny rachunek wymierny daje dwanaście okręgów czteropunktowych o
nośnikach

\[
\begin{gathered}
0123,\ 0145,\ 0167,\ 0246,\ 0257,\ 0347,\\
1256,\ 1346,\ 1357,\ 2345,\ 2367,\ 4567,
\end{gathered}                                           \tag{2.3}
\]

oraz osiem okręgów dokładnie trójpunktowych:

\[
035,\ 036,\ 056,\ 124,\ 127,\ 147,\ 247,\ 356.        \tag{2.4}
\]

Współliniowych trójek nie ma. Nośniki z (2.3) i (2.4) są parami różnymi,
a ich trójki dają

\[
12\binom43+8\binom33=48+8=56=\binom83.
\]

Pokrywają więc wszystkie trójki dokładnie raz. Konfiguracja wyznacza
dokładnie `12+8=20` okręgów i nie jest współokręgowa. Stąd

\[
f_{V3}(8)\le20.                                         \tag{2.5}
\]

Każde stwierdzenie w tej skończonej weryfikacji można sprawdzić przez
podstawienie do równania

\[
x^2+y^2+Ax+By+C=0.
\]

Do pakietu dołączony jest również audyt wykonujący ten rachunek wyłącznie
na ułamkach zwykłych.

## 3. Partycja trójek

Ustalmy dowolną konfigurację V3. Niech `c_s` oznacza liczbę maksymalnych
okręgów zawierających dokładnie `s` wybranych punktów, a

\[
m=\max\{s:c_s>0\}.
\]

Ponieważ żadne trzy punkty nie są współliniowe, każda trójka wyznacza jeden
właściwy okrąg. Dwie różne maksymalne podpory okręgów nie mogą zawierać tej
samej trójki. Dostajemy dokładną partycję

\[
\sum_{s=3}^{m}\binom{s}{3}c_s=\binom n3.               \tag{3.1}
\]

Liczba wszystkich wyznaczonych okręgów wynosi

\[
C=\sum_{s=3}^{m}c_s.                                   \tag{3.2}
\]

Ponieważ cały zbiór nie jest współokręgowy, zawsze `m<=n-1`.

## 4. Sumowany Melchior po inwersji

Potrzebujemy jednej klasycznej nierówności. Jeśli rzeczywisty,
niekolinearny zbiór punktów wyznacza `t_r` prostych zawierających dokładnie
`r` jego punktów, nierówność Melchiora ma postać

\[
t_2\ge 3+\sum_{r\ge4}(r-3)t_r.                         \tag{4.1}
\]

Krótki dowód wynika z dualności projektowej i wzoru Eulera. W dualnym
układzie prostych mamy

\[
V=\sum_{r\ge2}t_r,\qquad E=\sum_{r\ge2}r t_r.
\]

Każda komórka ma co najmniej trzy boki, więc `3F<=2E`. Ze wzoru Eulera
`V-E+F=1` dla płaszczyzny projektowej otrzymujemy `E<=3V-3`, co po
przeniesieniu składników jest dokładnie (4.1).

Teraz wybierzmy punkt `p` naszej konfiguracji i wykonajmy inwersję o środku
`p`. Pozostałe `n-1` punktów tworzą zbiór niekolinearny. Gdyby wszystkie
ich obrazy leżały na prostej nieprzechodzącej przez środek inwersji, punkty
pierwotne leżałyby na jednym okręgu przez `p`. Prosta przez środek
odpowiadałaby natomiast współliniowości co najmniej trzech punktów
pierwotnych. Obie możliwości są w V3 wykluczone.

Co więcej, żadna prosta wyznaczona przez dwa obrazy nie przechodzi przez
środek inwersji, ponieważ oznaczałoby to współliniowość tych dwóch punktów
z `p`. Każda taka prosta jest zatem obrazem właściwego okręgu przez `p`.

Okrąg z `s` wybranymi punktami, po odwróceniu względem jednego ze swoich
punktów, staje się prostą z `s-1` obrazami. Sumujemy (4.1) po wszystkich
`n` wyborach punktu `p`. Okrąg trójpunktowy trafia na lewą stronę trzy
razy. Okrąg czteropunktowy nie wnosi składnika karnego, a okrąg
`s`-punktowy dla `s>=5` wnosi `s(s-4)`. Dostajemy

\[
3c_3-\sum_{s=5}^{m}s(s-4)c_s\ge3n.                    \tag{4.2}
\]

To właśnie brak współliniowych trójek usuwa z (4.2) wszystkie składniki
pochodzące od prostych. W wariancie V1 ta sama operacja jest znacznie mniej
czysta.

## 5. Jedna kombinacja liniowa dla małych i średnich okręgów

Załóżmy `m>=4` i połóżmy

\[
A=\binom m3,\qquad B=m(m-4),\qquad D=3A+B,
\]

\[
\lambda_m=\frac{B+3}{D},\qquad
\mu_m=\frac{A-1}{D}.                                  \tag{5.1}
\]

Oba mnożniki są dodatnie.

Mnożymy (3.1) przez `lambda_m`, a (4.2) przez `mu_m`, po czym dodajemy.
Dla `s=3` współczynnik wynosi

\[
\lambda_m+3\mu_m=1,
\]

a dla `s=m`

\[
\lambda_m\binom m3-\mu_m m(m-4)=1.
\]

Dla każdego `4<=s<=m` dokładny zapas do współczynnika `1` jest równy

\[
1-\left(\lambda_m\binom s3-\mu_m s(s-4)\right)
=\frac{(m-s)(s-3)(ms-m-s-2)}{3m(m+2)}\ge0.            \tag{5.2}
\]

Wszystkie współczynniki po lewej stronie kombinacji są więc nie większe
od współczynników w `C=sum c_s`. Otrzymujemy uniwersalną granicę

\[
C\ge L(n,m):=\lambda_m\binom n3+3n\mu_m.              \tag{5.3}
\]

Po uproszczeniu

\[
L(n,m)=
\frac{n(3m^2+mn^2-3mn+2m-n^2+3n+4)}{3m(m+2)}.        \tag{5.4}
\]

Najważniejsza własność tej funkcji to monotoniczność względem `m`:

\[
L(n,m)-L(n,m+1)=
\frac{n(n-4)(n+1)(m^2-m-3)}
{3m(m+1)(m+2)(m+3)}>0                                \tag{5.5}
\]

dla używanego dalej zakresu `n>=5`, `m>=4`. Zamiast sprawdzać wiele
możliwych rozmiarów najbogatszego okręgu, wystarczy więc sprawdzić największy
z nich w rozpatrywanym przedziale.

## 6. Okrąg zawierający więcej niż połowę punktów

Niech `Gamma` będzie okręgiem z `m` punktami, a `k=n-m` punktów leży poza
nim. Dla każdego outsidera `x` rozważamy pióro okręgów wyznaczonych przez
`x` i parę punktów `Gamma`. W jednym piórze jest dokładnie \(\binom m2\)
różnych okręgów.

Dla dwóch outsiderów `x,y` wspólny okrąg obu piór musi używać tej samej
pary punktów `Gamma`. Dwa różne wspólne okręgi przechodzą już przez `x,y`,
więc odpowiadają rozłącznym parom na `Gamma`; w przeciwnym razie dwa różne
okręgi miałyby trzy wspólne punkty. Przecięcie dwóch piór ma zatem rozmiar
co najwyżej `floor(m/2)`.

Pierwsze dwa wyrazy zasady włączeń i wyłączeń, wraz z samym `Gamma`, dają

\[
C\ge P(n,m):=
1+k\binom m2-\binom k2\left\lfloor\frac m2\right\rfloor.
                                                               \tag{6.1}
\]

Załóżmy teraz `m>floor(n/2)`, czyli `1<=k<m`. Jeżeli `m=2r`, bezpośrednie
odejmowanie od `G(n)` daje

\[
2(P(n,2r)-G(n))=
(k-1)\bigl(4r^2-6r+2-k(r+1)\bigr).                  \tag{6.2}
\]

Dla `k<=2r-1` nawias jest nie mniejszy niż

\[
2r^2-7r+3=(2r-1)(r-3).
\]

Jeżeli `m=2r+1`, analogicznie

\[
2(P(n,2r+1)-G(n))=
(k-1)\bigl(4r^2-2r-k(r+1)\bigr),                    \tag{6.3}
\]

a dla `k<=2r` nawias jest nie mniejszy niż `2r(r-2)`.

Przy `n>=11` oba odpowiednie parametry spełniają `r>=3`. Z (6.2) i (6.3)
wynika więc

\[
P(n,m)\ge G(n)\qquad
(n\ge11,\ m>\lfloor n/2\rfloor).                    \tag{6.4}
\]

## 7. Wszystkie `n>=11`

Pozostał zakres `m<=floor(n/2)`. Dla `m=3` z (3.1) od razu mamy
\(C=\binom n3>G(n)\). Dla `m>=4` używamy (5.3) i monotoniczności (5.5).

Jeżeli `n=2r`, to `r>=6` i

\[
L(2r,r)-G(2r)=
\frac{(r-2)(2r^2-13r+2)}{3(r+2)}.                   \tag{7.1}
\]

Dla `r=6` prawa strona wynosi `-2/3`. Ponieważ `C` i `G(12)` są
całkowite, już `C>=L(12,6)=G(12)-2/3` daje `C>=G(12)`. Dla `r>=7`
licznik `2r^2-13r+2` jest dodatni, więc (7.1) jest jeszcze mocniejsze.

Jeżeli `n=2r+1`, to `r>=5` i

\[
L(2r+1,r)-G(2r+1)=
\frac{(2r-3)(r^3-4r^2-4r-2)}{3r(r+2)}.              \tag{7.2}
\]

Wielomian w drugim nawiasie ma dla `r=5` wartość `3`, a potem rośnie,
gdyż jego różnica kolejna wynosi `3r^2-5r-7>0`. Prawa strona (7.2) jest
więc dodatnia.

Granice (6.4), (7.1) i (7.2) obejmują wszystkie możliwe `m`. W połączeniu
z konstrukcją (2.1) dowodzą

\[
f_{V3}(n)=G(n)\qquad(n\ge11).                        \tag{7.3}
\]

## 8. Przypadki `n=4,5,6`

Dla `n=4` cały zbiór nie może leżeć na jednym okręgu. Każda z czterech
trójek daje zatem inny okrąg, więc `f_V3(4)=4`.

Dla `n=5`, jeśli `m=3`, partycja trójek daje \(C=\binom53=10\). Jeśli `m=4`,
okrąg czteropunktowy i jedyny outsider dają przez (6.1)

\[
C\ge1+\binom42=7.
\]

Konstrukcja z rozdziału 2 osiąga `7`, zatem `f_V3(5)=7`.

Dla `n=6` przypadki `m=3` i `m=5` dają odpowiednio `20` i co najmniej
\(1+\binom52=11\) okręgów. Niech `m=4`. Dwa różne okręgi czteropunktowe mają
co najwyżej dwa wspólne wybrane punkty. Ich dwupunktowe dopełnienia w
zbiorze sześciopunktowym muszą być więc rozłączne. Stąd `c_4<=3`.
Z (3.1)

\[
20=c_3+4c_4,
\]

więc

\[
C=c_3+c_4=20-3c_4\ge11.
\]

Konstrukcja osiąga tę wartość i `f_V3(6)=11`.

## 9. Przypadek `n=7` i przeszkoda Fano

Dla `m=6` granica (6.1) daje `16`, a dla `m=5` daje `19`. Dla `m=3`
mamy `35`. Pozostaje `m=4`.

Z partycji trójek

\[
35=c_3+4c_4,
\qquad
C=35-3c_4.                                           \tag{9.1}
\]

Dopełnienia podpór dwóch różnych okręgów czteropunktowych są trójkami
mającymi co najwyżej jeden wspólny punkt. Ich pary są zatem rozłączne, co
daje \(3c_4\le\binom72=21\), a więc `c_4<=7`.

Równość `c_4=7` oznaczałaby, że siedem trójkowych dopełnień zużywa każdą
parę dokładnie raz. Byłby to system Steinera `STS(7)`, czyli płaszczyzna
Fano. Taki układ podpór okręgów nie ma realizacji nad liczbami rzeczywistymi.
Poniżej podajemy krótki dowód potrzebnej przeszkody.

Każdy punkt `(x_i,y_i)` podnosimy do wektora

\[
v_i=(x_i,y_i,x_i^2+y_i^2,1)\in\mathbb R^4.           \tag{9.2}
\]

Macierz tych wektorów ma rangę `4`: hiperpłaszczyzna zawierająca wszystkie
kolumny oznaczałaby, że wszystkie punkty leżą na jednym okręgu albo prostej.
Cztery kolumny są zależne dokładnie wtedy, gdy odpowiadające punkty leżą na
jednym okręgu, ponieważ współliniowych trójek nie ma. Gale'owski dual
macierzy z (9.2) miałby rangę `3`, a dopełnienia siedmiu zależnych czwórek
byłyby jego siedmioma zależnymi trójkami. Nie byłoby innych zależnych
trójek, bo odpowiadałyby dodatkowym okręgom czteropunktowym. Otrzymalibyśmy
więc rzeczywistą reprezentację płaszczyzny Fano.

Żeby zobaczyć sprzeczność bez odwołania do klasyfikacji matroidów, oznaczmy
linie Fano jako

\[
123,\ 145,\ 167,\ 246,\ 257,\ 347,\ 356.             \tag{9.3}
\]

Punkty `1,2,4` nie tworzą linii, więc ich wektory można przyjąć za bazę:
`v_1=(1,0,0)`, `v_2=(0,1,0)`, `v_4=(0,0,1)`. Z pierwszych trzech
odpowiednich linii zapiszmy

\[
v_3=(a,b,0),\qquad v_5=(c,0,d),\qquad v_6=(0,e,f),   \tag{9.4}
\]

gdzie wszystkie sześć współczynników jest niezerowych. Linie `167`, `257`
i `347` wymuszają dla `v_7=(X,Y,Z)` zależności

\[
\frac{Y}{Z}=\frac{e}{f},\qquad
\frac{X}{Z}=\frac{c}{d},\qquad
\frac{X}{Y}=\frac{a}{b}.
\]

Stąd `bcf=ade`. Ostatnia linia `356` wymaga natomiast

\[
\det(v_3,v_5,v_6)=-aed-bcf=0.
\]

Po podstawieniu dostajemy `2ade=0`, co jest niemożliwe nad
\(\mathbb R\). Zatem `c_4=7` nie zachodzi i faktycznie `c_4<=6`. Z (9.1)
wynika `C>=17` w gałęzi `m=4`.

Najmniejszą granicę ze wszystkich gałęzi daje więc `m=6`, czyli `16`.
Konstrukcja z rozdziału 2 ją osiąga:

\[
f_{V3}(7)=16.                                         \tag{9.5}
\]

## 10. Przypadek `n=8`

Dla `m=4` podstawienie `n=8,m=4` do (5.3) daje

\[
C\ge L(8,4)=20.                                      \tag{10.1}
\]

Dla `m=5,6,7` granica (6.1) daje kolejno `25,28,22`, a dla `m=3` mamy
`C=56`. Każda konfiguracja V3 ośmiu punktów wyznacza zatem co najmniej
`20` okręgów. Wymierna konfiguracja (2.2) osiąga `20`, więc

\[
f_{V3}(8)=20.                                         \tag{10.2}
\]

To jedyny wyjątek od funkcji `G(n)`.

## 11. Przypadek `n=9`

Dla `m=4` równania (3.1) i (4.2) przyjmują postać

\[
84=c_3+4c_4,\qquad 3c_3\ge27.
\]

Pierwsze z nich daje `c_3=0 mod 4`, dlatego `c_3>=12`. W konsekwencji

\[
C=c_3+c_4=21+\frac34c_3\ge30.                        \tag{11.1}
\]

Dla `m=5,6,7,8` granica (6.1) daje odpowiednio `29,37,40,29`, a dla
`m=3` mamy `84`. Najmniejsza możliwa wartość to co najmniej `29`, osiągana
przez konstrukcję z ośmioma punktami na okręgu i outsiderem. Zatem

\[
f_{V3}(9)=29.                                         \tag{11.2}
\]

## 12. Przypadek `n=10`

Dla `m=3` partycja (3.1) daje \(C=\binom{10}{3}=120\). Dla `m=4` granica
(5.3) daje `L(10,4)=75/2`, zatem całkowitość `C` daje `C>=38`. Dla
`m=6,7,8,9` granica (6.1) daje kolejno `43,55,53,37`. Pozostaje `m=5`.

Najpierw pokażemy, że w rzeczywistej konfiguracji dziesięciu punktów nie
może istnieć sześć różnych maksymalnych okręgów pięciopunktowych. Dla
pięcioelementowej podpory `A` w dziesięcioelementowym zbiorze połóżmy

\[
y_A=\mathbf1_A-\frac12\mathbf1.
\]

Dwie różne podpory okręgów przecinają się w co najwyżej dwóch punktach.
Dlatego

\[
\|y_A\|^2=\frac52,
\qquad
\langle y_A,y_B\rangle=|A\cap B|-\frac52\le-\frac12.
\]

Dla rodziny `q` pięciopunktowych okręgów

\[
0\le\left\|\sum_Ay_A\right\|^2
\le\frac q2(6-q).                                    \tag{12.1}
\]

Stąd `q<=6`. Gdyby `q=6`, w (12.1) wszędzie zachodziłaby równość: każda
para podpór przecinałaby się w dwóch punktach, a każdy z dziesięciu punktów
należałby do dokładnie trzech podpór.

Oznaczmy sześć okręgów przez `A_1,...,A_6`, a punktowi `p` przypiszmy
trójkę indeksów

\[
I(p)=\{i:p\in A_i\}.
\]

Każdy indeks występuje pięć razy, a każda para indeksów dwa razy. Dziesięć
trójek `I(p)` jest różnych. Gdyby na przykład `123` wystąpiła dwa razy,
pary `12,13,23` byłyby już wyczerpane. Każdy z indeksów `1,2,3`
potrzebowałby jeszcze trzech wystąpień, których nie można łączyć ze sobą;
wymagałoby to dziewięciu dalszych punktów zamiast dostępnych ośmiu.

Po ustaleniu jednej trójki `123` prosty bilans przecięć z nią wymusza trzy
trójki spotykające ją w dwóch indeksach i sześć spotykających ją w jednym.
Pierwsze trzy mają postać `12a,13b,23c`, gdzie `a,b,c` są różnymi
elementami zbioru `{4,5,6}`. Gdyby na przykład `a=b=4`, para `14`
wystąpiłaby już dwa razy. Indeks `1` potrzebowałby jeszcze dwóch trójek,
ale nie mogłyby one użyć `2`, `3` ani `4`; obie musiałyby więc być równe
`156`, wbrew różności trójek. Pozostałe zlania są symetryczne.

Po zmianie nazw możemy przyjąć `a=4,b=5,c=6`. Dla indeksu `1` resztowe
stopnie par `14,15,16` wynoszą `1,1,2`, więc dwie brakujące trójki to
`146,156`. Dla indeksu `2` analogicznie otrzymujemy `245,256`, a dla
indeksu `3` — `345,346`. Cały układ jest zatem wymuszony:

\[
\begin{gathered}
123,\ 124,\ 135,\ 236,\\
146,\ 156,\ 245,\ 256,\ 345,\ 346.                  \tag{12.2}
\end{gathered}
\]

Odwróćmy płaszczyznę względem punktu `123`. Okręgi `A_1,A_2,A_3`
przechodzą w trzy proste. Pierwsza i druga przecinają się w obrazie punktu
`124`, pierwsza i trzecia w obrazie `135`, a druga i trzecia w obrazie
`236`. Są to trzy różne wybrane punkty. Proste nie są więc równoległe ani
współpękowe i tworzą niezdegenerowany trójkąt. Oznaczmy

\[
A=124,\quad B=135,\quad C=236,
\]

oraz

\[
X=146,\ Y=156,\ U=245,\ V=256,\ W=345,\ Z=346.
\]

Punkty `X,Y` leżą na `AB`, punkty `U,V` na `AC`, a `W,Z` na `BC`.
Pozostałe trzy okręgi mają podpory

\[
\begin{aligned}
A_4&: A,X,U,W,Z,\\
A_5&: B,Y,U,V,W,\\
A_6&: C,X,Y,V,Z.                                    \tag{12.3}
\end{aligned}
\]

Wprowadźmy skierowane parametry afiniczne na bokach:

\[
\begin{aligned}
AB:&\quad A=0,\ B=1,\ X=x,\ Y=y,\\
AC:&\quad A=0,\ C=1,\ U=u,\ V=v,\\
BC:&\quad B=0,\ C=1,\ W=w,\ Z=z.
\end{aligned}
\]

Niech `c^2=|AB|^2`, `b^2=|AC|^2`, `a^2=|BC|^2`. Sześciokrotne użycie
twierdzenia o potędze punktu dla okręgów z (12.3) daje

\[
\begin{aligned}
c^2(1-x)&=a^2wz,\\
b^2(1-u)&=a^2(1-w)(1-z),\\
c^2y&=b^2uv,\\
a^2(1-w)&=b^2(1-u)(1-v),\\
c^2xy&=b^2v,\\
c^2(1-x)(1-y)&=a^2z.                                \tag{12.4}
\end{aligned}
\]

Wszystkie dzielone dalej czynniki są niezerowe, bo żaden nazwany punkt nie
jest końcem swojego boku. Z (12.4) kolejno wynika

\[
x=\frac1u,\qquad 1-y=\frac1w,\qquad
1-z=\frac1{1-v}.                                    \tag{12.5}
\]

Po oznaczeniu `R=b^2/c^2`, `S=a^2/c^2` pierwsze potrzebne równania dają

\[
R=\frac{w-1}{wuv},\qquad
S=\frac{(u-1)(v-1)}{uwv}.                            \tag{12.6}
\]

Podstawiamy (12.6) do czwartego równania w (12.4). Jego strony, po
podzieleniu przez `c^2`, są odpowiednio

\[
-\frac{(u-1)(v-1)(w-1)}{uwv}
\quad\text{oraz}\quad
+\frac{(u-1)(v-1)(w-1)}{uwv}.
\]

Wspólna wartość bez znaku jest niezerowa. Sprzeczność dowodzi, że przypadek
`q=6` nie istnieje nad liczbami rzeczywistymi. Zatem

\[
c_5\le5.                                              \tag{12.7}
\]

W gałęzi `m=5` mamy

\[
120=c_3+4c_4+10c_5,
\qquad
3c_3-5c_5\ge30.                                      \tag{12.8}
\]

Dla kolejnych `c_5=0,1,2,3,4,5` warunek podzielności w pierwszym równaniu
i drugie równanie wymuszają odpowiednio `c_3>=12,14,16,18,20,22`. W każdym
przypadku

\[
C=c_3+c_4+c_5\ge39.                                  \tag{12.9}
\]

Najmniejsza dolna granica we wszystkich gałęziach to zatem `37`, osiągana
przez dziewięć punktów na okręgu i outsidera. Ostatecznie

\[
f_{V3}(10)=37.                                        \tag{12.10}
\]

## 13. Koniec dowodu i granica certyfikacji

Rozdziały 7–12 obejmują wszystkie `n>=4`, a rozdział 2 dostarcza konstrukcji
osiągających każdą podaną wartość. Twierdzenie jest udowodnione.

Sam dowód dla `n>=11` opiera się tylko na partycji trójek, inwersji,
elementarnej postaci nierówności Melchiora, kombinacji liniowej (5.1) i
liczeniu piór (6.1). Dwa rzeczywiste małe obstruktory są zapisane w całości:
dualna przeszkoda Fano dla `n=7` oraz przeszkoda z potęgi punktu dla sześciu
pięciopunktowych okręgów przy `n=10`.

Skrypt

```powershell
python erdos506_v3_complete_audit.py --last-n 2000
```

sprawdza dokładnie:

1. wszystkie wyświetlone tożsamości algebraiczne;
2. wymierną konstrukcję `n=8`, brak współliniowych trójek i pełną partycję
   jej `56` trójek na `20` okręgów;
3. arytmetykę przypadków `n=4,...,10`;
4. redundantny skan wszystkich gałęzi `(n,m)` do zadanego `n`.

Skan skończony nie zastępuje argumentu dla nieskończonego zakresu. Ten
zakres zamykają symboliczne wzory (5.2), (5.5), (6.2), (6.3), (7.1) i
(7.2). Program nie formalizuje topologicznego dowodu Melchiora ani kroków
geometrii rzeczywistej w rozdziałach 9 i 12; ich dowody są podane w tekście,
a osobne starsze audyty pozostają kontrolą redundantną.

Użyta postać nierówności Melchiora pochodzi z: E. Melchior, *Über Vielseite
der projektiven Ebene*, Deutsche Mathematik 5 (1940), 461–475. Kontekst
samego problemu i rozróżnienie jego wariantów opisuje strona
[Erdős Problems #506](https://www.erdosproblems.com/506). Stwierdzenie tutaj jest wynikiem lokalnego pakietu
V3; nie jest deklaracją pierwszeństwa publikacyjnego ani zastępstwem
niezależnej recenzji matematycznej.
