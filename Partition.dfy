/*===============================================
  M.EIC037: Formal Methods For Critical Systems

  Project 2 

  Your name(s): 
  Pedro
  Bruno
  José

  ===============================================*/

method dutch_national_flag(a: array<int>, p: int) returns (lt: int, gt: int)
  modifies a
  ensures 0 <= lt <= gt <= a.Length
  ensures forall i :: 0 <= i < lt ==> a[i] < p
  ensures forall i :: lt <= i < gt ==> a[i] == p
  ensures forall i :: gt <= i < a.Length ==> a[i] > p
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var low,mid, high_ptr := 0, 0, a.Length - 1;

  lt := 0; // Will be updated to `low` at the end
  gt := 0; // Will be updated to `mid` (or `high_ptr + 1` depending on interpretation) at the end

  while mid <= high_ptr
    invariant 0 <= low <= mid 
    invariant mid <= high_ptr + 1 // high_ptr can become -1, mid can become a.Length
    invariant high_ptr < a.Length 
    invariant forall k :: 0 <= k < low ==> a[k] < p
    invariant forall k :: low <= k < mid ==> a[k] == p
    invariant forall k :: high_ptr < k < a.Length ==> a[k] > p //in high_ptr we cannot guarantee a[][k] > p, only high_ptr + 1
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases high_ptr - mid + 1
  {
    if a[mid] < p {
      if low < mid { // Ensure we are actually swapping different elements
        a[low], a[mid] := a[mid], a[low];
      } else { // if low == mid, a[mid] is already a[low]
        // No actual data movement needed for a[low], but a[mid] is processed.
      }
      low := low + 1;
      mid := mid + 1;
    } else if a[mid] == p {
      mid := mid + 1;
    } else { // a[mid] > p
      // The swap is fine even if mid == high_ptr, it just swaps with itself.
      a[mid], a[high_ptr] := a[high_ptr], a[mid];
      high_ptr := high_ptr - 1;
      // mid is not incremented here because the element swapped into a[mid]
      // from a[high_ptr] has not yet been processed.
    }
  }
  lt := low;
  // After the loop, elements a[low..mid-1] are == p.
  // So, the region for '== p' is from 'low' up to 'mid-1'.
  // 'gt' should be the start of the '> p' region, which is 'mid'
  // (or high_ptr + 1, which should be equal to mid at this point if all elements were processed).
  gt := mid; 
}