import re
import os
from os.path import join
from lxml import etree

verbose = True

for filename in os.listdir("html/Contrasimulation"):
	if not filename.endswith("html") or filename.startswith("index"):
		continue
	if verbose:
		print(filename)
	xml = etree.parse(join("html/Contrasimulation/", filename))

	defs = xml.xpath("//*[text()='locale' or text()='definition' or text()='inductive' or text()='coinductive'  or text()='lemma'  or text()='theorem'  or text()='corollary' or text()='abbreviation']/..")
	for d in defs:
		name = d.tail.strip()
		if verbose:
			print(name)
		if name:
			d.set('id', name)
	
	with open(join("html/Contrasimulation/", filename), "w") as xmlOut:
  		xmlOut.write(etree.tostring(xml, encoding='utf-8', pretty_print=True))
