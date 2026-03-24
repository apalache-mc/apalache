Fix "used before it is assigned" error when using grouped-variable UNCHANGED with nested operator references (e.g., `vars == <<myList1, myList2>>` where `myList1 == <<myVar1, myVar2>>`), see #3143

