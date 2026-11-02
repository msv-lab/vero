import Huffman.Impl.Build
#check (Huffman.buildf_witness : Huffman.BuildfSig)
#check (Huffman.obuildf_witness : Huffman.ObuildfSig)
#eval (Huffman.buildf_witness Nat id [.leaf 9, .leaf 2, .leaf 1] (by simp)).val
#print axioms Huffman.buildf_witness
#print axioms Huffman.obuildf_witness
