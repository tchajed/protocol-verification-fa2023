// There's no code to write for this exercise. After installing Dafny, open
// this file and confirm you see a verification error. (You might also want to
// try to figure out on your own what the error means, but we'll teach you the
// syntax more gradually in the next chapter.)

lemma MyFirstFalseLemma(z: int)
  ensures z + 1 > z
  ensures 2 * z >= z
{
  if z < 0 {
    assert 2 * z >= z;
  } else {
    assert 2 * z >= z;
  }
}
