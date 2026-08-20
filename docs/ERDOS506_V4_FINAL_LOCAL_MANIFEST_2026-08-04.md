# Erdős #506 V4 — finalny manifest lokalny

Data zamrożenia: 4 sierpnia 2026.

## Zakres

Pakiet dotyczy wyłącznie zamrożonego wariantu `V4`: `n>=4` różnych punktów
rzeczywistej płaszczyzny, nie wszystkie współliniowe, żadne cztery na jednym
właściwym okręgu euklidesowym. Liczymy różne właściwe okręgi zawierające
niewspółliniowe trójki wybranych punktów. Prostych nie liczymy.

Warunek „nie wszystkie współliniowe” jest częścią twierdzenia. Bez niego
minimum wynosiłoby `0`. Dodanie mocniejszego warunku „żadne trzy
współliniowe” tworzyłoby inny, trywialny wariant o wartości `binom(n,3)`.

## Zamknięty wynik

Lokalny pakiet dowodzi dla każdego `n>=4`

\[
\boxed{f_{V4}(n)=\binom{n-1}{2}}.
\]

Wartości dla `n=4,...,10` to

\[
3,6,10,15,21,28,36.
\]

## Aktywny łańcuch dowodowy

Pełna narracja znajduje się w
`docs/ERDOS506_V4_COMPLETE_PROOF_2026-08-04.md`.

Zakaz czterech punktów współokręgowych sprawia, że dwie różne
niewspółliniowe trójki nie mogą wyznaczać tego samego okręgu. Liczba
okręgów jest więc dokładnie liczbą niewspółliniowych trójek.

Jeżeli wybrana prosta zawiera `m` punktów, a poza nią leży `k=n-m`, liczymy
trójki zawierające dwa punkty tej prostej oraz trójki zawierające jeden jej
punkt i dwa punkty zewnętrzne. Otrzymujemy

\[
T\ge k\binom m2+\binom k2(m-1)
=\frac{k(m-1)(n-1)}2.
\]

Dokładny zapas nad celem wynosi

\[
\frac{n-1}{2}(k-1)(m-2)\ge0.
\]

Konstrukcja z `n-1` punktami na jednej prostej i jednym outsiderem osiąga
równość. Każdy jej właściwy okrąg zawiera outsidera i dokładnie dwa punkty
prostej, więc warunek V4 jest spełniony.

Dowód nie korzysta z V1, V3, nierówności Melchiora ani żadnego zewnętrznego
twierdzenia incydencyjnego.

## Pliki autorytatywne

Dowód:

`docs/ERDOS506_V4_COMPLETE_PROOF_2026-08-04.md`

Dokładny checker:

`erdos506_v4_complete_audit.py`

Zamrożony wynik checkera:

`docs/erdos506_v4_complete_audit_2026-08-04.json`

Test regresyjny:

`tests/test_erdos506_v4_complete_audit.py`

## Odtworzenie

Z katalogu głównego repozytorium:

```powershell
python erdos506_v4_complete_audit.py --last-n 500
python -m pytest -q tests\test_erdos506_v4_complete_audit.py
python -m py_compile erdos506_v4_complete_audit.py tests\test_erdos506_v4_complete_audit.py
python -m ruff check erdos506_v4_complete_audit.py tests\test_erdos506_v4_complete_audit.py
```

## Wyniki kontroli

Główny audyt zakończył się kodem `0`. Sprawdził wszystkie `124 250` par
`(n,m)` dla `4<=n<=500`, symboliczne tożsamości oraz dokładne konstrukcje
dla `n=4,5,6,8,10,20,30`. W każdej konstrukcji największa podpora okręgu
ma rozmiar `3`.

Skupiony test V4 zakończył się wynikiem `4 passed`. `py_compile` zakończył
się kodem `0`, a Ruff wynikiem `All checks passed!`. Checker celowo odrzuca
uruchomienie przez `python -O`, ponieważ ten tryb usuwa asercje.

Końcowy wspólny przebieg nowych pakietów V3 i V4 zakończył się wynikiem
`9 passed`. Istniejący niezależny moduł `circle_key.py` potwierdził dla
konstrukcji V4 przy `n=12`: `55` różnych okręgów, `165` współliniowych
trójek i rozkład podpór `{3: 55}`.

Zapisany JSON został porównany semantycznie z bieżącym wynikiem funkcji
`audit(500)` i kontrola zwróciła `V4_JSON_SEMANTIC_MATCH_PASS`.

## Granica certyfikacji

Checker wyznacza konstrukcje na ułamkach zwykłych, normalizuje równania
okręgów, kontroluje ich pełne podpory i sprawdza faktoryzację symboliczną.
Nie jest formalizacją w systemie Lean lub Coq. Skan do `n=500` jest kontrolą
redundantną; dowód wszystkich `n` stanowi jawna nieujemna faktoryzacja.

Pakiet jest kompletnym lokalnym rozwiązaniem dokładnie zdefiniowanego V4.
Nie zgłasza pierwszeństwa publikacyjnego i nie zmienia wyników V1 ani V3.

## Wiązanie SHA-256

Ostateczne hashe znajdują się w
`docs/ERDOS506_V4_FINAL_LOCAL_MANIFEST_2026-08-04.sha256`. Plik `.sha256`
nie wiąże własnego hasha.
