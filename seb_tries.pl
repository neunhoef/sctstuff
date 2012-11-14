
foreach (35..60) {
	$s = "TrySeveral([" . $_ . "],30);";
	print "\n\n######" . $s . "######\n\n";
	open(P,"|gap seb.g");
	print P $s . "\nQUIT;\n";
	close(P);
}

