// TODO: votes should be Seq[Int]
fn count_votes(votes: Seq, candidate: Int, low: Int, hight: Int) -> Int
  requires 0 <= low, low <= high, high <= votes
{
  if low == high {
    0
  } else {
    count_votes(votes, candidate, low, high - 1) +
      if votes[high - 1] == candidate {
        1
      } else {
        0
      }
  }
}
