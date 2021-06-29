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

	defs = xml.xpath("//*[text()='locale' or text()='definition' or text()='inductive' or text()='primrec' or text()='coinductive'  or text()='lemma'  or text()='theorem'  or text()='corollary' or text()='abbreviation']/..")
	for d in defs:
		name = d.tail.strip()
	
		if name:
			if verbose:
				print(name)
			d.set('id', name)
		else:
			nameNode = d.getnext()
			if verbose:
				print(nameNode.text)
			if nameNode.text:
				nameNode.set('id', nameNode.text)
	
	with open(join("html/Contrasimulation/", filename), "w") as xmlOut:
  		xmlOut.write(etree.tostring(xml, encoding='utf-8', pretty_print=True))
