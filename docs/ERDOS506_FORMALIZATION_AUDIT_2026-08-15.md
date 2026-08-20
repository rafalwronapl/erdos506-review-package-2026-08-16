# Audyt formalizacji V1/V3/V4 po bramce wydania

Data stanu: 2026-08-15.

## Najkrótszy werdykt

Źródłowe publiczne endpointy V1 i V3 nie przyjmują już struktur zasad
geometrii rzeczywistej ani callbacków przypadków skończonych. Target V3 oraz
wskazane niżej moduły topologii i geometrii projektywnej przeszły buildy
Leana 4.30.0 z przypiętym mathlib 4.30.0.

Końcowa bramka została wykonana po zapisaniu pierwotnego checkpointu:
`Erdos506.V1.Main` przeszedł 8885 zadań, umbrella build `Erdos506` przeszedł
8888 zadań, a strict `AxiomsAudit.lean` zakończył się pomyślnie. Jest to
lokalnie zweryfikowany snapshot gotowy do recenzji technicznej i matematycznej;
nie jest to jeszcze roszczenie publikacyjne ani o pierwszeństwo.

## Publiczne sygnatury źródłowe

Publiczny master V1 ma postać:

```lean
Erdos506.V1.circleCount_ge_v1Target
    (cfg : Configuration alpha)
    (hadm : Admissible cfg)
    (hcard : 4 <= Fintype.card alpha)
```

Konstruuje wewnętrznie Melchiora, zasadę parzystej aranżacji, ograniczony
Kelly--Moser, radical-axis cross-block oraz dane geometrii skończonej. Dawny
parametr Langera zastępuje podział na skończone okno `14..22` i duży ogon.
Jest to stwierdzenie o aktualnej sygnaturze źródła; jego końcowy wynik builda
jest zielony.

Publiczny dolny endpoint V3 to:

```lean
Erdos506.V3.circleCount_ge_target
    (cfg : Configuration alpha)
    (hcard : 4 <= Fintype.card alpha)
    (hadm : Admissible cfg)
```

V3 konstruuje `RealPlaneMelchiorPrinciple` wewnętrznie. Ten target przeszedł
bieżący build. V4 pozostaje bezwarunkowym twierdzeniem w swoim zamrożonym
modelu; jego stan nie był przedmiotem nowego residualu z 15 sierpnia.

## Wyniki już zweryfikowane

| Polecenie | Stan | Uwagi |
| --- | --- | --- |
| `lake -Kjobs=1 build Erdos506.V1.Main` | **PASS** | `8885` jobs; parameter-free V1 |
| `lake -Kjobs=1 build Erdos506` | **PASS** | `8888` jobs; umbrella root V1/V3/V4 |
| `lake env lean -DwarningAsError=true AxiomsAudit.lean` | **PASS** | publiczny audyt aksjomatów |
| `lake build Erdos506.V3.Main` | **PASS** | parameter-free dolne oszacowanie V3 i jego zależności |
| `lake build Erdos506.Incidence.RealProjectiveArrangementEulerFinish` | **PASS** | `8511/8511`; projektowy Euler/insertion po naprawie instancji topologicznych |
| `lake build Erdos506.Incidence.RealProjectiveTriangleCrossingSign Erdos506.Incidence.RealProjectiveTriangleExit` | **PASS** | `8505/8505`; tylko ostrzeżenia lintera `unnecessarySeqFocus` |

W obu modułach trójkąta wykonano również lokalny skan pod `sorry`,
`admit` i deklaracje `axiom`; nie znaleziono dopasowań. Nie zastępuje to
jeszcze pełnego skanu ani publicznego audytu całego drzewa.
