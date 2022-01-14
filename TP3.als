sig Hash {}

abstract sig Object {
	hash : one Hash
}

sig Blob extends Object {}

sig Name {}

sig Tree extends Object {
	objects : Hash -> Name
}

sig Commit extends Object {
	tree : one Hash,
	parent : set Hash
}

pred Invs {
	all t : Tree, n : Name | lone (t.objects.n)
    	all h, o1, o2 : univ | o1 -> h in hash and o2 -> h in hash implies o1 = o2
    	all t : Tree | all h : Hash | h in t.objects.Name implies h in Tree.hash + Blob.hash 
    	all c : Commit | all h : Hash | h in c.tree implies h in Tree.hash
    	all c : Commit | all h : Hash | h in c.parent implies h in Commit.hash
  	all c : Commit | c not in c.^(parent.~hash)
  	all t : Tree | t not in t.^(objects.Name.~hash)
    	all t1, t2: Tree | t1.objects = t2.objects implies t1 = t2
    	all c1, c2: Commit | c1.tree = c2.tree and c1.parent = c2.parent implies c1 = c2
}
