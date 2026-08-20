# Erdős #506, wariant V4: pełne rozwiązanie lokalne

Data: 4 sierpnia 2026.

## 1. Zamrożona definicja

Wariant `V4` oznacza tutaj dokładnie:

1. `n` punktów rzeczywistej płaszczyzny jest różnych;
2. nie wszystkie punkty leżą na jednej prostej;
3. żaden właściwy okrąg euklidesowy nie zawiera czterech wybranych punktów;
4. liczymy różne właściwe okręgi zawierające co najmniej jedną
   niewspółliniową trójkę wybranych punktów.

Prostych ani „okręgów o nieskończonym promieniu” nie liczymy. Dla `n>=4`
warunek trzeci automatycznie wyklucza współokręgowość całego zbioru.

Niech `f_V4(n)` będzie najmniejszą możliwą liczbą wyznaczonych okręgów.

## 2. Wynik

**Twierdzenie.** Dla każdego całkowitego `n>=4`

\[
\boxed{f_{V4}(n)=\binom{n-1}{2}}.                    \tag{2.1}
\]

Ten sam wzór jest prawdziwy również dla `n=3`, jeśli wymagamy, żeby trzy
punkty nie były współliniowe.

## 3. Okręgi są tym samym co niewspółliniowe trójki

Niech `T` oznacza liczbę niewspółliniowych trójek wybranych punktów. Każda
taka trójka wyznacza jeden właściwy okrąg.

Dwie różne trójki nie mogą wyznaczać tego samego okręgu. Ich suma zawiera
co najmniej cztery różne punkty, a wspólny okrąg byłby wtedy sprzeczny z
definicją V4. Odwzorowanie

\[
\{\text{niewspółliniowe trójki}\}
\longrightarrow
\{\text{wyznaczone okręgi}\}
\]

jest więc bijekcją. Liczba okręgów `C` spełnia dokładnie

\[
C=T.                                                   \tag{3.1}
\]

Cały problem V4 sprowadza się zatem do elementarnego pytania: ile co
najmniej niewspółliniowych trójek ma niekolinearny zbiór `n` punktów?

## 4. Dolna granica

Wybierzmy dowolną prostą `ell` wyznaczoną przez dwa punkty konfiguracji.
Niech leży na niej dokładnie `m` wybranych punktów, a poza nią

\[
k=n-m.
\]

Mamy `m>=2` oraz `k>=1`, ponieważ cały zbiór nie jest współliniowy.

Najpierw wybieramy dwa punkty z `ell` i jeden punkt spoza niej. Każda taka
trójka jest niewspółliniowa, co daje

\[
k\binom m2                                             \tag{4.1}
\]

trójek.

Następnie wybieramy dwa punkty `x,y` spoza `ell`. Prosta `xy` przecina
`ell` w co najwyżej jednym punkcie. Spośród `m` punktów na `ell` co
najmniej `m-1` tworzy więc z `x,y` niewspółliniową trójkę. Ten drugi rodzaj
daje co najmniej

\[
\binom k2(m-1)                                        \tag{4.2}
\]

trójek. Rodzaje (4.1) i (4.2) są rozłączne. Trójek złożonych wyłącznie z
punktów spoza `ell` nie musimy nawet liczyć. Stąd

\[
\begin{aligned}
T
&\ge k\binom m2+\binom k2(m-1)\\
&=\frac{k(m-1)(n-1)}2.                               \tag{4.3}
\end{aligned}
\]

Porównujemy to z wartością z twierdzenia:

\[
\begin{aligned}
T-\binom{n-1}{2}
&\ge\frac{n-1}{2}\bigl(k(m-1)-(n-2)\bigr)\\
&=\frac{n-1}{2}(k-1)(m-2)\\
&\ge0.                                                \tag{4.4}
\end{aligned}
\]

Z (3.1) wynika

\[
C\ge\binom{n-1}{2}.                                  \tag{4.5}
\]

Zauważmy, że nie wybieraliśmy najbogatszej prostej. Argument działa dla
dowolnej prostej przechodzącej przez dwa wybrane punkty.

## 5. Konstrukcja osiągająca granicę

Weźmy `n-1` punktów

\[
(0,0),(1,0),\ldots,(n-2,0)
\]

na prostej `y=0` oraz jeden punkt

\[
u=(0,1)
\]

poza nią. Zbiór nie jest współliniowy.

Każdy właściwy okrąg przecina prostą `y=0` w co najwyżej dwóch punktach.
Ponieważ poza tą prostą wybraliśmy tylko `u`, żaden okrąg nie zawiera
czterech punktów konfiguracji. Konstrukcja spełnia więc definicję V4.

Trójki punktów z `y=0` są współliniowe i nie wyznaczają właściwych
okręgów. Każda para punktów z tej prostej wraz z `u` wyznacza okrąg. Dwie
różne pary nie mogą dać tego samego okręgu, bo taki okrąg zawierałby co
najmniej trzy różne punkty prostej `y=0`.

Liczba wyznaczonych okręgów jest dokładnie

\[
\binom{n-1}{2}.                                      \tag{5.1}
\]

Granice (4.5) i (5.1) dowodzą twierdzenia.

## 6. Dlaczego warunek o prostych musi być zapisany

Nazwa „V4” bez warunku liniowego oznacza trzy różne problemy.

Jeżeli wolno położyć wszystkie punkty na jednej prostej, konfiguracja
spełnia zakaz czterech punktów na właściwym okręgu, ale nie wyznacza żadnego
okręgu. Minimum wynosi wtedy `0`.

Jeżeli oprócz zakazu czterech punktów współokręgowych wymagamy, aby żadne
trzy punkty nie były współliniowe, każda z \(\binom n3\) trójek jest
niewspółliniowa i każda wyznacza inny okrąg. Minimum — a właściwie wartość
każdej dopuszczalnej konfiguracji — wynosi wtedy

\[
\binom n3.
\]

Wersja rozwiązana w tym dokumencie leży pomiędzy tymi skrajnościami:
wyklucza tylko pełną współliniowość i dlatego ma dokładną wartość
\(\binom{n-1}{2}\).

## 7. Audyt wykonywalny

Skrypt

```powershell
python erdos506_v4_complete_audit.py --last-n 500
```

sprawdza symbolicznie tożsamości (4.3)–(4.4), wszystkie pary `(n,m)` do
podanego `n` oraz dokładne wymierne konstrukcje bliskiego pęku. Dla każdej
testowanej konstrukcji wyznacza wszystkie trójki, oddziela współliniowe i
normalizuje równania okręgów w arytmetyce wymiernej.

Skan skończony nie jest podstawą dowodu dla wszystkich `n`; tę rolę pełni
tożsamość (4.4). Pakiet jest samowystarczalny i nie importuje żadnego
twierdzenia zewnętrznego ani wyniku V1 lub V3.
