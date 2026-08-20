# Erdős #506 (V1): korekta przypadku `n=6`

**Data:** 2026-08-10  
**Status:** korekta aktywna; zastępuje wszystkie wcześniejsze tezy
`f_V1(6)=9`.

## Poprawna wartość

W konwencji V1 — sześć różnych punktów rzeczywistej płaszczyzny, nie
wszystkie współliniowe ani współokręgowe, przy liczeniu różnych właściwych
okręgów zawierających niewspółliniową trójkę wybranych punktów — zachodzi

\[
\boxed{f_{V1}(6)=8}.
\]

Dolna granica `8` wynika z naprawionego argumentu dla jedynego potencjalnego
przypadku z co najwyżej siedmioma okręgami; poniższa konfiguracja wymierna
osiąga tę granicę.

## Dokładny świadek wymierny

Niech

~~~text
p0 = (0,0)       p1 = (4,0)       p2 = (1,0)
p3 = (1,3)       p4 = (2/5,6/5)   p5 = (2,2).
~~~

Punkty są parami różne. Punkty `p0,p1,p3` są niewspółliniowe, więc cały
zbiór nie leży na prostej. Z kolei `p0,p1,p2` są trzema różnymi punktami
jednej prostej, zatem żaden właściwy okrąg nie zawiera wszystkich sześciu
punktów. Świadek jest więc dopuszczalny w V1.

Dokładnie współliniowe trójki etykiet to

~~~text
012, 034, 135.
~~~

Pozostałych trójek jest `binom(6,3)-3=17`. Wszystkie wyznaczone przez nie
okręgi są ujęte w następującym censusie. Równania są zapisane w postaci
`x^2+y^2+D*x+E*y+G=0`; kolumna „punkty” podaje pełny ślad okręgu na
konfiguracji.

| nr | równanie | punkty |
|---:|---|---|
| 1 | `x^2+y^2-5x-3y+4=0` | `1,2,3,4` |
| 2 | `x^2+y^2-5x-y+4=0` | `1,2,5` |
| 3 | `x^2+y^2-4x-2y=0` | `0,1,3` |
| 4 | `x^2+y^2-4x=0` | `0,1,4,5` |
| 5 | `x^2+y^2-3x-2y+2=0` | `2,4,5` |
| 6 | `x^2+y^2-2x-4y+4=0` | `3,4,5` |
| 7 | `x^2+y^2-x-3y=0` | `0,2,3,5` |
| 8 | `x^2+y^2-x-y=0` | `0,2,4` |

Podstawienie sześciu par współrzędnych do każdego równania daje dokładnie
wskazany ślad. Trzy okręgi czteropunktowe pokrywają po cztery
niewspółliniowe trójki, a pięć okręgów trzypunktowych po jednej, czyli
łącznie `3*4+5=17`. Dwa różne właściwe okręgi nie mogą zawierać tej samej
niewspółliniowej trójki. Census jest zatem wyczerpujący i świadek wyznacza
dokładnie osiem właściwych okręgów.

## Dolna granica `C>=8`

Niech `C` oznacza liczbę właściwych okręgów. Standardowa partycja trójek i
nierówności Melchiora redukują założenie `C<=7` do jednego przypadku.

- Okrąg pięciopunktowy daje co najmniej dziewięć okręgów, a przypadek, w
  którym wszystkie właściwe okręgi są trzypunktowe, daje co najmniej
  dziesięć. Największy okrąg musiałby więc mieć cztery punkty.
- Prosta cztero- lub pięciopunktowa daje przez rachunek outsider-pencil co
  najmniej dziesięć okręgów, więc wszystkie bogate proste mają rozmiar trzy.
- Niech `b=C_4`, `L=L_3`, a `B_3` liczy wszystkie maksymalne uogólnione
  bloki trzypunktowe. Wtedy

  ~~~text
  B_3+4b=20,                 C=20-3b-L.
  ~~~

  Zsumowany pivot-Melchior daje `b<=3`, a Melchior dla pierwotnych prostych
  daje `L<=4`. Warunek `C<=7` wymusza więc `b=3` i `L=4`.
- Równość we wszystkich lokalnych luzach wymusza konfigurację Pascha:
  cztery trójproste tworzą pełny czworokąt, każdy punkt leży na dwóch z
  nich, a trzy czteropunktowe okręgi mają jako dopełnienia trzy pary
  diagonalne. Po etykietowaniu prostych jako `012,034,135,245` podpory
  okręgów są wymuszone jako `0145,0235,1234`.

Ostatni wzorzec nie ma realizacji euklidesowej. Wolno użyć podobieństwa, więc
przy zachowaniu okręgów można przyjąć

~~~text
p0=(0,0),   p1=(1,0),   p3=(u,v),   v!=0,
p2=(a,0),   p4=b(u,v),
p5=t(1,0)+(1-t)(u,v),   t=a(b-1)/(b-a),
~~~

Z różności punktów `a,b` są niezerowe i `a,b!=1`. Ponadto `a!=b`: dla
`a=b` proste `p2p4` i `p1p3` byłyby równoległe i różne, choć obie miałyby
zawierać afiniczny punkt `p5`. Oznaczmy
`R=u^2+v^2>0`. Dokładne wyznaczniki współokręgowości wymuszonych podpór,
po odrzuceniu jawnych niezerowych czynników, dają kolejno

~~~text
a(1-2u)+bR=0,
a+b(R-2u)=0,
a-bR=0.
~~~

Z trzeciego równania `a=bR`. Drugie daje wtedy `2b(R-u)=0`, czyli `R=u`.
Pierwsze redukuje się do `2bR(1-u)=0`, więc `u=1`. Ostatecznie
`R=u=1` i `R=u^2+v^2` dają `v=0`, wbrew normalizacji. Wszystkie trzy
tożsamości wyznacznikowe są sprawdzane symbolicznie w poprawionym audycie
Pythona. Zatem `C<=7` jest niemożliwe i `C>=8`. W połączeniu z censussem
świadka otrzymujemy `f_V1(6)=8`.

## Źródło błędu w starej wartości `9`

Stare raporty wysyłały trzy niewspółliniowe punkty do
`(0,0),(1,0),(0,1)` za pomocą dowolnej transformacji afinicznej, a następnie
stosowały standardowe euklidesowe równania współokręgowości. Transformacja
afiniczna zachowuje współliniowość, lecz na ogół wysyła okrąg na elipsę;
współokręgowość zachowują użyte w poprawionym dowodzie podobieństwa, nie
dowolne mapy afiniczne. Stary rachunek nie miał więc prawa przyjąć
jednocześnie `E=F` i `D=0`.

Dla świadka powyżej afiniczne współrzędne względem
`p0`, `u=p1-p0=(4,0)` i `v=p3-p0=(1,3)` wynoszą

~~~text
p2=(1/4,0),   p4=(0,2/5),   p5=(1/3,2/3),
E=16,         F=10,          D=4.
~~~

W oznaczeniach starego raportu jest więc `a=1/4`, `b=2/5`, `s=1/3`.
Podane tam rzekome warunki trzech rzeczywistych czterookręgów przyjmują
wartości

~~~text
b+2s-1 = 1/15,   a-2s+1 = 7/12,   a-b = -3/20,
~~~

chociaż census powyżej sprawdza dokładnie podpory `0145`, `0235` i `1234`.
To jest bezpośredni kontrtest dla użytych w starym raporcie równań po
normalizacji.

Jest to dokładnie realizowalny „triangle side-point pattern”, który stary
rachunek błędnie wykluczał po zastąpieniu tej macierzy Grama macierzą
jednostkową. Nie wpływa to na argumenty używające wyłącznie incidencji; psuje
konkretnie euklidesowy krok współokręgowości po niedozwolonej normalizacji.

## Status formalizacji

Stan na koniec tego raportu jest następujący.

- [`formalization/Erdos506/Targets.lean`](../formalization/Erdos506/Targets.lean)
  definiuje poprawny wyjątek `v1Target 6 = 8`; twierdzenie
  `v1Target_small_values` sprawdza listę `[3,5,8,11,17]`.
- `Targets.lean`, `V1/SmallBasic.lean` i `V1/SmallReduction.lean` przeszły
  `lake env lean -DwarningAsError=true` z kodem wyjścia `0`.
- Naprawiony, bezpieczny euklidesowo moduł
  [`formalization/Erdos506/V1/SmallSix.lean`](../formalization/Erdos506/V1/SmallSix.lean).
  Przeszedł
  `lake env lean -DwarningAsError=true Erdos506/V1/SmallSix.lean` z kodem `0`
  i obejmuje `six_terminal_census` (arytmetycznie
  `B3=8,b=3,L=4,C=7` z wierszy terminalnych), `pasch_three_circles_algebra`,
  `pasch_parameter_relations`, `no_pasch_three_circle_pattern` oraz
  etykietowany adapter `no_labelled_pasch_three_circle_pattern`. Kernel
  zachowuje parametry `E,F,D` zamiast utożsamiać dowolną bazę afiniczną z
  bazą ortonormalną.
- Pełne publiczne twierdzenie end-to-end dla dolnej granicy `n=6` znajduje
  się w
  [`formalization/Erdos506/V1/SmallSixClassifier.lean`](../formalization/Erdos506/V1/SmallSixClassifier.lean).
  `exists_paschPencilLabels` klasyfikuje abstrakcyjny `BlockSystem` przy
  `C<=7`, `no_geometric_paschPencilLabels` wykonuje transfer do bezpiecznego
  metrycznie terminalu, a `circleCount_ge_target_of_card_six` kończy dowód
  `8<=circleCount`. Punktowy typecheck, modułowy build, publiczny build,
  `AxiomsAudit.lean`, skan higieny i niezależny hostile review przeszły.
  Audyt aksjomatów raportuje wyłącznie `propext`, `Classical.choice` i
  `Quot.sound`.
- Poprawiony audyt Pythona
  [`erdos506_n6_survivor_geometry.py`](../erdos506_n6_survivor_geometry.py)
  używa progu `C<=7`, pozostawia jedną orbitę Pascha, symbolicznie sprawdza
  wyznaczniki w normalizacji przez podobieństwo oraz odtwarza dokładny census
  świadka `C=8`; skrypt przechodzi. Jest to audyt odtwarzalności, nie
  samodzielny maszynowy certyfikat całej dolnej granicy; pełny krok
  support-forcing jest teraz niezależnie sformalizowany w
  `SmallSixClassifier.lean`.

Szczegóły ogólnej granicy Lean rejestruje aktualny
[`ERDOS506_FORMALIZATION_AUDIT_2026-08-10.md`](ERDOS506_FORMALIZATION_AUDIT_2026-08-10.md).
Plik `SESSION_CHECKPOINT_2026-08-10_V1_HALFCAP_COMPLETE.md` pozostaje jedynie
historycznym checkpointem śród-sesyjnym.

Oddzielny audyt argumentów dla `n=7,...,14` nie znalazł powtórzenia błędu
„dowolna normalizacja afiniczna, a następnie metryczny wniosek o okręgach”.
Sam ten dawny audyt nie był nowym dowodem tych przypadków. Od czasu jego
wykonania osobne moduły Lean domknęły endpointy dolnej granicy `n=7,8,14`;
szczegóły podaje aktualny audyt formalizacji.

Ta korekta dotyczy V1. Nie zmienia osobnych wartości ani dowodów wariantów
V3 i V4, a formuła V1 dla `n>=9` pozostaje bez zmian.
