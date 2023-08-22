
(* Very explicit *)
#[local] Arguments binddt {M}%type_scope (T U)%function_scope {Binddt}   G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
#[local] Arguments mapdt  {M}%type_scope (T)%function_scope   {Mapdt}    G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
#[local] Arguments bindd  {M}%type_scope (T U)%function_scope {Bindd}                               (A B)%type_scope _%function_scope _.
#[local] Arguments mapd   {M}%type_scope (T)%function_scope   {Mapd}                                (A B)%type_scope _%function_scope _.
#[local] Arguments bindt                 (T U)%function_scope {Bindt}    G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
#[local] Arguments traverse              (T)%function_scope   {Traverse} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
#[local] Arguments bind                  (T U)%function_scope {Bind}                                (A B)%type_scope _%function_scope _.
#[local] Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope _.
#[local] Arguments ret T%function_scope {Return} A%type_scope _.
#[local] Arguments cobind W%function_scope {Cobind} (A B)%type_scope _%function_scope _.

(* Halfway explicit *)
#[local] Arguments binddt {M}%type_scope T {U}%function_scope {Binddt}   G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[local] Arguments mapdt  {M}%type_scope (T)%function_scope   {Mapdt}    G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[local] Arguments bindd  {M}%type_scope T {U}%function_scope {Bindd}                               {A B}%type_scope _%function_scope _.
#[local] Arguments mapd   {M}%type_scope (T)%function_scope   {Mapd}                                {A B}%type_scope _%function_scope _.
#[local] Arguments bindt                 T {U}%function_scope {Bindt}    G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[local] Arguments traverse              (T)%function_scope   {Traverse} G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[local] Arguments bind                  (T) {U}%function_scope {Bind}                              {A B}%type_scope _%function_scope _.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments ret T%function_scope {Return} {A}%type_scope _.
#[local] Arguments cobind W%function_scope {Cobind} {A B}%type_scope _%function_scope _.

#[local] Arguments binddt {M}%type_scope {T U}%function_scope {Binddt}   G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
#[local] Arguments mapdt  {M}%type_scope (T)%function_scope   {Mapdt}    G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
#[local] Arguments bindd  {M}%type_scope {T U}%function_scope {Bindd}                               (A B)%type_scope _%function_scope _.
#[local] Arguments mapd   {M}%type_scope (T)%function_scope   {Mapd}                                (A B)%type_scope _%function_scope _.
#[local] Arguments bindt                 {T U}%function_scope {Bindt}    G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
#[local] Arguments traverse              (T)%function_scope   {Traverse} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
#[local] Arguments bind                  {T U}%function_scope {Bind}                                (A B)%type_scope _%function_scope _.
#[local] Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope _.
