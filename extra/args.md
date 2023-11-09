
(* Very explicit *)
#[local] Arguments binddt (W)%type_scope (U T)%function_scope {Binddt}   G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
#[local] Arguments mapdt  (E)%type_scope (T)%function_scope   {Mapdt}    G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
#[local] Arguments bindd  (W)%type_scope (U T)%function_scope {Bindd}                               (A B)%type_scope _%function_scope _.
#[local] Arguments mapd   (E)%type_scope (T)%function_scope   {Mapd}                                (A B)%type_scope _%function_scope _.
#[local] Arguments cobind (W)%function_scope                  {Cobind}                              (A B)%type_scope _%function_scope _.
#[local] Arguments bindt                 (U T)%function_scope {Bindt}    G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
#[local] Arguments traverse              (T)%function_scope   {Traverse} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
#[local] Arguments bind                  (U T)%function_scope {Bind}                                (A B)%type_scope _%function_scope _.
#[local] Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope _.
#[local] Arguments ret T%function_scope {Return} A%type_scope _.

(* Halfway explicit *)
#[local] Arguments binddt (W)%type_scope {U} (T)%function_scope {Binddt}   G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[local] Arguments mapdt  {E}%type_scope (T)%function_scope   {Mapdt}    G%function_scope {H H0 H1}   {A B}%type_scope _%function_scope _.
#[local] Arguments bindd  {W}%type_scope {U} (T)%function_scope {Bindd}                               {A B}%type_scope _%function_scope _.
#[local] Arguments mapd   {E}%type_scope (T)%function_scope   {Mapd}                                  {A B}%type_scope _%function_scope _.
#[local] Arguments cobind {W}%function_scope                  {Cobind}                                {A B}%type_scope _%function_scope _.
#[local] Arguments bindt                 {U} (T)%function_scope {Bindt}    G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[local] Arguments traverse              (T)%function_scope   {Traverse} G%function_scope {H H0 H1}   {A B}%type_scope _%function_scope _.
#[local] Arguments bind                  {U} (T)%function_scope {Bind}                                {A B}%type_scope _%function_scope _.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments ret T%function_scope {Return} {A}%type_scope _.

(* Totally implicit *)
#[local] Arguments binddt {W}%type_scope {U} {T}%function_scope {Binddt}   G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[local] Arguments mapdt  {E}%type_scope {T}%function_scope   {Mapdt}    G%function_scope {H H0 H1}   {A B}%type_scope _%function_scope _.
#[local] Arguments bindd  {W}%type_scope {U} {T}%function_scope {Bindd}                               {A B}%type_scope _%function_scope _.
#[local] Arguments mapd   {E}%type_scope {T}%function_scope   {Mapd}                                  {A B}%type_scope _%function_scope _.
#[local] Arguments cobind {W}%function_scope                  {Cobind}                                {A B}%type_scope _%function_scope _.
#[local] Arguments bindt                 {U} {T}%function_scope {Bindt}    G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[local] Arguments traverse              {T}%function_scope   {Traverse} G%function_scope {H H0 H1}   {A B}%type_scope _%function_scope _.
#[local] Arguments bind                  {U} {T}%function_scope {Bind}                                {A B}%type_scope _%function_scope _.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments ret T%function_scope {Return} {A}%type_scope _.



#[local] Arguments runBatch (A B)%type_scope F%function_scope {H H0 H1} ϕ%function_scope C%type_scope b.
#[local] Arguments runBatch {A B}%type_scope F%function_scope {H H0 H1} ϕ%function_scope C%type_scope b.
#[local] Arguments runBatch {A B}%type_scope F%function_scope {H H0 H1} ϕ%function_scope {C}%type_scope b.
#[local] Arguments runBatch {A B}%type_scope {F}%function_scope {H H0 H1} ϕ%function_scope {C}%type_scope b.
