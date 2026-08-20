# Erdős #506 V3 — finalny manifest lokalny

Data zamrożenia: 4 sierpnia 2026.

## Zakres

Pakiet dotyczy wyłącznie wariantu `V3`: `n>=4` różnych punktów rzeczywistej
płaszczyzny, żadne trzy współliniowe, nie wszystkie współokręgowe; liczone są
różne właściwe okręgi euklidesowe zawierające co najmniej jedną trójkę
wybranych punktów. Prostych nie liczymy.

To inny wariant niż główny lokalny pakiet `V1`, w którym współliniowe trójki
są dozwolone. Wyników V1 i V3 nie wolno mieszać.

## Zamknięty wynik

Lokalny pakiet dowodzi

\[
f_{V3}(n)=
\begin{cases}
20,&n=8,\\
1+\binom{n-1}{2},&n\ge4,\ n\ne8.
\end{cases}
\]

Małe wartości to

\[
4,7,11,16,20,29,37
\]

dla `n=4,...,10`.

## Aktywny łańcuch dowodowy

Pełna polska narracja znajduje się w
`docs/ERDOS506_V3_COMPLETE_PROOF_2026-08-04.md`.

Dla każdej konfiguracji liczby `c_s` maksymalnych okręgów `s`-punktowych
spełniają partycję trójek

\[
\sum_s\binom s3c_s=\binom n3
\]

oraz, po inwersji kolejno względem każdego punktu i zsumowaniu nierówności
Melchiora,

\[
3c_3-\sum_{s\ge5}s(s-4)c_s\ge3n.
\]

Jedna jawna dodatnia kombinacja tych dwóch zależności daje funkcję
`L(n,m)` dla maksymalnego rozmiaru okręgu `m`. Jej symbolicznie sprawdzona
monotoniczność zamyka wszystkie gałęzie `m<=floor(n/2)` dla `n>=11`.
Elementarne liczenie piór względem najbogatszego okręgu daje `P(n,m)` i
zamyka wszystkie gałęzie `m>floor(n/2)`.

Zakres `n=4,...,10` jest rozpisany oddzielnie. Jedynymi nietrywialnymi
rzeczywistymi końcówkami są dualna przeszkoda Fano przy `n=7` oraz
przeszkoda z potęgi punktu wykluczająca sześć okręgów pięciopunktowych przy
`n=10`. Oba argumenty są zawarte w pełnym dowodzie. Starsze dokumenty
`docs/ERDOS506_N7_F11_PROOF_2026-07-30.md` i
`scratch/n10_gamma5_analytic_closure_20260804/SIX_FIVEBLOCK_POWER_OBSTRUCTION.md`
pozostają kontrolą redundantną, a nie ukrytym źródłem dodatkowych założeń.

Górna granica standardowa pochodzi z `n-1` punktów na okręgu i jednego
ogólnego outsidera. Wyjątek `n=8` osiąga jawna konfiguracja wymierna z
dwunastoma okręgami czteropunktowymi i ośmioma trójpunktowymi.

## Pliki autorytatywne

Dowód:

`docs/ERDOS506_V3_COMPLETE_PROOF_2026-08-04.md`

Samowystarczalny audyt dokładny:

`erdos506_v3_complete_audit.py`

Wynik audytu:

`docs/erdos506_v3_complete_audit_2026-08-04.json`

Test regresyjny:

`tests/test_erdos506_v3_complete_audit.py`

Red-team matematyczny:

`scratch/v3_complete_redteam_20260804/AGENT1_MATHEMATICAL_REDTEAM.md`

Red-team certyfikatu:

`scratch/v3_complete_redteam_20260804/AGENT2_CERTIFICATE_REDTEAM.md`

## Odtworzenie

Z katalogu głównego repozytorium:

```powershell
python erdos506_v3_complete_audit.py --last-n 2000
python -m pytest -q tests\test_erdos506_v3_complete_audit.py
python -m py_compile erdos506_v3_complete_audit.py tests\test_erdos506_v3_complete_audit.py
python -m ruff check erdos506_v3_complete_audit.py tests\test_erdos506_v3_complete_audit.py
```

Audyt główny używa arytmetyki wymiernej dla konstrukcji `n=8` i SymPy dla
tożsamości wielomianowych. Skan do `n=2000` jest redundantną kontrolą
implementacji. Dowód nieskończonego zakresu nie zależy od końca tego skanu.

## Wyniki kontroli

Audyt główny z `--last-n 2000` zakończył się kodem `0`. Sprawdził `1 994 975`
par `(n,m)` dla `11<=n<=2000` oraz `124 250` redundantnych współczynników.

Nowy test V3 zakończył się wynikiem `5 passed`. Końcowy przebieg łączący go
z istniejącym audytem Fano zakończył się wynikiem `6 passed`.
`py_compile` zakończył się kodem `0`, a Ruff wynikiem
`All checks passed!`. Próba uruchomienia checkera przez `python -O` jest
celowo odrzucana, ponieważ ten tryb usuwa asercje certyfikatu.

Istniejący niezależny moduł `circle_key.py`, który wyznacza okręgi dwiema
innymi normalizacjami wyznacznika, również zwrócił dla konstrukcji `n=8`:
osiem różnych punktów, zero współliniowych trójek, dwadzieścia okręgów oraz
rozkład podpór `{3: 8, 4: 12}`.

Istniejący dokładny audyt dualnej przeszkody Fano i jego test zakończyły się
powodzeniem. Oba red-teamy zwróciły `PASS`; po naprawieniu wszystkich pięciu
uwag klasy `MINOR` oba wykonały kontrolę poprawek i ponownie zwróciły
`PASS`. Nie było uwag `BLOCKER` ani `MAJOR`.

Ostatni pełny test całego repozytorium, wykonany przed dodaniem
izolowanego pakietu V3, miał wynik `744 passed, 1 skipped`; nowy pakiet ma
osobny wynik skupiony podany wyżej.

## Granica certyfikacji

Checker formalizuje dokładną konstrukcję wymierną, wszystkie wyświetlone
tożsamości algebraiczne, arytmetykę małych przypadków i redundantny duży
skan. Nie jest formalizacją w systemach Lean ani Coq. Topologiczny dowód
nierówności Melchiora, dualność Gale'a, argument z potęgi punktu i przejścia
inwersyjne są dowodami ludzkimi zapisanymi w tekście.

Pakiet jest lokalnie zamkniętym dowodem V3 z odtwarzalnymi kontrolami. Nie
jest jeszcze zewnętrznie zrecenzowaną publikacją i nie stanowi deklaracji
pierwszeństwa. Przed publicznym zgłoszeniem potrzebne są niezależna recenzja
matematyczna oraz osobny, szeroki przegląd literatury dla dokładnie tej
definicji V3.

## Wiązanie SHA-256

Ostateczne hashe znajdują się w pliku
`docs/ERDOS506_V3_FINAL_LOCAL_MANIFEST_2026-08-04.sha256`. Należy je liczyć
dopiero po wprowadzeniu wszystkich poprawek red-teamów. Sam plik `.sha256`
nie wiąże własnego hasha.
