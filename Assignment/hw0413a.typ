#let myblock(body) = block(fill: rgb("#efe"), inset: 1em, radius: 1em, width: 90%)[#body]

#myblock[
```
//@ require true
//@ ensure l * l <= n < (l + 1) * (l + 1)
x = n;
l = 0;
r = n + 1;
// @[generated] x = n && l = 0 && r = n + 1 && n >= 0
//@ inv l * l <= n < r * r && l + 1 <= r && x == n
while (l + 1 < r) do {
/* @[generated]
	l * l <= n < r * r && l + 1 <= r && x == n &&
	l + 1 < r
*/
	mid = (l + r) / 2;
/* @[generated]
	l * l <= n < r * r && l + 1 <= r && x == n &&
	l + 1 < r && mid = (l + r) / 2
*/
	if (x < mid * mid) then {
/* @[generated]
	l * l <= n < r * r && l + 1 <= r && x == n &&
	l + 1 < r && mid = (l + r) / 2 && x < mid * mid
*/
			r = mid
/* @[generated]
	l * l <= n < r2 * r2 && l + 1 <= r2 && x == n &&
	l + 1 < r2 && mid = (l + r2) / 2 && x < mid * mid &&
	r = mid
*/
	} else {
/* @[generated]
	l * l <= n < r * r && l + 1 <= r && x == n &&
	l + 1 < r && mid = (l + r) / 2 && !(x < mid * mid)
*/
		l = mid
/* @[generated]
	l2 * l2 <= n < r * r && l2 + 1 <= r && x == n &&
	l2 + 1 < r && mid = (l2 + r) / 2 && !(x < mid * mid) &&
	l = mid
*/
	}
/* @[generated]
	(l * l <= n < r2 * r2 && l + 1 <= r2 && x == n &&
	l + 1 < r2 && mid = (l + r2) / 2 && x < mid * mid &&
	r = mid) ||
	(l2 * l2 <= n < r * r && l2 + 1 <= r && x == n &&
	l2 + 1 < r && mid = (l2 + r) / 2 && !(x < mid * mid) &&
	l = mid)
*/
// @[target] l * l <= n < r * r && l + 1 <= r && x == n
}
/* @[generated]
	l * l <= n < r * r && l + 1 <= r && x == n &&
	!(l + 1 < r)
*/
// @[target] l * l <= n < (l + 1) * (l + 1)

```
]

== 生成的验证条件

1.
#myblock[
```cpp
  (x = n && l = 0 && r = n + 1 && n >= 0)
  ->
  (l * l <= n < r * r && l + 1 <= r && x == n)
  ```
]

2.

#myblock[
```cpp
(
  (l * l <= n < r2 * r2 && l + 1 <= r2 && x == n &&
  l + 1 < r2 && mid = (l + r2) / 2 && x < mid * mid &&
  r = mid) ||
  (l2 * l2 <= n < r * r && l2 + 1 <= r && x == n &&
  l2 + 1 < r && mid = (l2 + r) / 2 && !(x < mid * mid) &&
  l = mid)
) -> (l * l <= n < r * r && l + 1 <= r && x == n)
```
]

3.
#myblock[
```cpp
(
	l * l <= n < r * r && l + 1 <= r && x == n && !(l + 1 < r)
) -> l * l <= n < (l + 1) * (l + 1)
```
]