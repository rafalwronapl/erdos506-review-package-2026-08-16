# Checkpoint V1: publiczny master bez parametrów geometrycznych

Data: 2026-08-15.

## Osiągnięty stan

Publiczny endpoint

```lean
Erdos506.V1.circleCount_ge_v1Target
```

przyjmuje już wyłącznie konfigurację, jej dopuszczalność oraz założenie
`4 ≤ Fintype.card α`. Nie przyjmuje `RealPlaneLangerPrinciple` ani żadnej
innej struktury zasad geometrycznych.

Dowód składa lokalnie Melchiora, parzystą aranżację, ograniczony Kelly--Moser,
radical-axis cross-block oraz geometrie dla przypadków 10--13. Zakres
`14 ≤ n ≤ 22` jest zamknięty przez
`v1UniformTarget_le_circleCount_finiteWindow_without_langer`, a `n ≥ 23`
przez istniejący cap-sensitive Melchior tail.

## Ostatni domknięty przypadek

Ostatnim residualem był wybrany blok liniowy `(n,s)=(15,6)`. Publiczny
endpoint

```lean
FiniteWindowRichBlockResidual.line_impossible_of_fifteen_six
```

eliminuje bloki rozmiaru siedem, zachowuje lokalny slack funkcjonału `108`
i uzyskuje `W ≥ 138`, podczas gdy uniwersalna pojemność daje `W ≤ 108`.
Nie korzysta z wcześniejszej, niebezpiecznej partycji nachodzących na siebie
rodzin okręgów.

## Nowe końcowe moduły

- `V1/LangerApplicationFifteenLineSixFinish.lean` -- ostatni residual;
- `V1/LangerApplicationFiniteWindowFinal.lean` -- bezwarunkowy dispatcher
  wszystkich przypadków 14--22;
- `V1/LangerApplicationAssembly.lean` -- sklejenie hard core, okna i ogona;
- `V1/Main.lean` -- publiczny master bez parametru Langera.

## Granica weryfikacji

Zmiany zostały najpierw sprawdzone statycznie, a następnie zweryfikowane
seryjnym buildem Lean. Aktualna bramka zakończyła się:

1. `lake -Kjobs=1 build Erdos506.V1.Main` -- PASS, 8885 jobs;
2. `lake -Kjobs=1 build Erdos506` -- PASS, 8888 jobs;
3. `lake env lean -DwarningAsError=true AxiomsAudit.lean` -- PASS;
4. aktualizacja bieżącego audytu i dokumentacji.

Pozostają zewnętrzna recenzja matematyczna, audyt literatury i przygotowanie
świeżego pakietu recenzenckiego. Nie należy przedstawiać wyniku jako roszczenia
o pierwszeństwo przed zakończeniem tych etapów.
