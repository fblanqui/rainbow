<?xml version="1.0" encoding="iso-8859-1"?>

<!-- This xsl-file transforms xml-proofs from AProVE into
     Rainbow's xml-format.
-->

<!-- author: thiemann, ulrichsg -->
<!-- version: $Id$ -->

<!-- TODO:
     - generate header of rainbow
     - testing, especially after RRR has been added one should
          test correct behaviour if function symbols that have been 
          deleted are reused as tuple-symbols
-->

<xsl:transform
                xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
                xmlns:exslt="http://exslt.org/common"
                xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
                xsi:schemaLocation="urn:rainbow.proof.format http://color.loria.fr/proof.xsd"
                exclude-result-prefixes="exslt"             
                version="2.0">
  <!-- WARNING: adding  xmlns="urn:rainbow.proof.format" as additional attribute above
                results in incorrect generated xml-files -->

  <xsl:output method="xml" indent="yes" omit-xml-declaration="no" />


<!-- **************************************************************************************** 
     **  starting point of the transformation, here the signature is extracted
     **  as signature of the root node in the proof!
     **************************************************************************************** -->
  <xsl:template match="/proof-obligation/proposition[basic-obligation]">
  <!-- proof xmlns="urn:rainbow.proof.format"
             xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
             xsi:schemaLocation="urn:rainbow.proof.format http://color.loria.fr/proof.xsd" -->
    <xsl:variable name="signature">
      <xsl:call-template name="sig_extract"/> <!-- select="basic-obligation/*[1]/*[1]"/ -->
    </xsl:variable>
    <xsl:choose>
      <xsl:when test="count(//qtrs-nontermination-proof) &gt; 0">
        <xsl:apply-templates select="//qtrs-nontermination-proof[1]"/>
      </xsl:when>
      <xsl:when test="count(//qsrs-nontermination-proof) &gt; 0">
        <xsl:apply-templates select="//qsrs-nontermination-proof[1]"/>
      </xsl:when>
      <xsl:when test="count(//reltrs-nontermination-proof) &gt; 0">
        <xsl:apply-templates select="//reltrs-nontermination-proof[1]"/>
      </xsl:when>
      <xsl:when test="count(//relsrs-nontermination-proof) &gt; 0">
        <xsl:apply-templates select="//relsrs-nontermination-proof[1]"/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates mode="trs" select=".">
          <xsl:with-param name="signature" select="$signature"/>
        </xsl:apply-templates>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  

<!-- **************************************************************************************** 
     **  currently the TRS/DP-problem-data is only implicit, so it is ignored
     **************************************************************************************** -->
  <xsl:template match="basic-obligation">
  </xsl:template>




<!-- **************************************************************************************** 
     **  General structure of the proof
     **  (2 modes: when working on DPs (default) tuple-symbols and signature are needed
     **            when working on TRSs (mode=trs) only the signature is needed)
     **************************************************************************************** -->
  <xsl:template match="proposition">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="signature"/>
    <proof>
     <xsl:apply-templates select="proof">
       <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
       <xsl:with-param name="signature" select="$signature"/>
     </xsl:apply-templates>
    </proof>
  </xsl:template>

  <!-- when working on TRSs no tuple-symbols have to be passed -->
  <xsl:template mode="trs" match="proposition">
    <xsl:param name="signature"/>
    <xsl:variable name="tagName">
      <xsl:choose>
        <xsl:when test="count(proof/qtrs-nontermination-proof) &gt; 0">counter_example</xsl:when>
        <xsl:otherwise>proof</xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:element name="{$tagName}">
     <xsl:apply-templates select="proof">
       <xsl:with-param name="signature" select="$signature"/>
     </xsl:apply-templates>
    </xsl:element>
  </xsl:template>
  
  <!-- for proofs that do not emit a <proof> tag themselves, such as ETRStoRelTRS -->
  <xsl:template mode="trs-noprooftag" match="proposition">
    <xsl:param name="signature"/>
    <xsl:apply-templates select="proof">
      <xsl:with-param name="signature" select="$signature"/>
    </xsl:apply-templates>
  </xsl:template>
  
<!-- **************************************************************************************** 
     **  SRS as TRS proof (dummy proof only used for inserting <as_trs/> tag)
     **************************************************************************************** -->
<xsl:template match="srs-as-trs-proof">
  <xsl:param name="signature"/>
  <as_trs>
    <xsl:apply-templates select="../../proof-obligation">
      <xsl:with-param name="signature" select="$signature"/>
    </xsl:apply-templates>
  </as_trs>
</xsl:template> 

<!-- **************************************************************************************** 
     **  SRS reversal proof
     **************************************************************************************** -->
<xsl:template match="qtrs-reverse-proof">
  <xsl:param name="signature"/>
  <reverse>
    <xsl:apply-templates select="../../proof-obligation">
      <xsl:with-param name="signature" select="$signature"/>
    </xsl:apply-templates>
  </reverse>
</xsl:template>

<xsl:template match="reltrs-reverse-proof">
  <xsl:param name="signature"/>
  <reverse>
    <xsl:apply-templates select="../../proof-obligation">
      <xsl:with-param name="signature" select="$signature"/>
    </xsl:apply-templates>
  </reverse>
</xsl:template>

<!-- **************************************************************************************** 
     **  TRS-to-DPs proof
     **  here is the point where the map from defined to tuple-symbols is generated
     **  this map has to be provided throughout the remaining proof
     **************************************************************************************** -->
  <xsl:template match="qtrs-dependency-pairs-proof">
    <xsl:param name="signature"/>
    <dp>
      <proof>
        <mark_symbols>
          <xsl:apply-templates 
            select="../../proof-obligation">
            <xsl:with-param name="signature" select="$signature"/>
            <xsl:with-param name="tuple-symbols">
              <defined-to-tuple>
                <!-- we add some more structure with orig/tuple, than just using symbol[1/2] -->
                <xsl:for-each select="defined-to-tuple-entry">
                  <entry>
                    <orig><xsl:copy-of select="symbol[1]"/></orig>
                    <tupled><xsl:copy-of select="symbol[2]"/></tupled>
                  </entry>
                </xsl:for-each>
              </defined-to-tuple>
            </xsl:with-param>
          </xsl:apply-templates>
        </mark_symbols>
      </proof>
    </dp>
  </xsl:template>



<!-- **************************************************************************************** 
     **  SCC-decomposition
     **  in the children one has to provide one pair of the SCCs for identification
     **  moreover, currently only root-symbols are compared for edge-deletion, here
     **  no information is necessary 
     **************************************************************************************** -->
  <xsl:template match="qdp-dependency-graph-proof">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="signature"/>
    <decomp>
      <graph>
        <unif/>
      </graph>
      <xsl:apply-templates mode="scc" select="../../proof-obligation">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        <xsl:with-param name="signature" select="$signature"/>
      </xsl:apply-templates>
    </decomp>
  </xsl:template>
  
  <xsl:template mode="scc" match="proposition">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="signature"/>
    <component>
      <xsl:apply-templates mode="onePair" select="basic-obligation">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
      <xsl:if test="count(proof/non-scc) = 0">
        <proof>
          <xsl:apply-templates select="proof">   
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
            <xsl:with-param name="signature" select="$signature"/>
          </xsl:apply-templates>
        </proof>
      </xsl:if>
    </component>
  </xsl:template>
  

  <xsl:template mode="onePair" match="qdp">
    <xsl:param name="tuple-symbols"/>
    <rules>
      <xsl:apply-templates select="dps/rule">   
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
    </rules>
  </xsl:template>

<!-- **************************************************************************************** 
     **  No DPs / rules left proof
     **************************************************************************************** -->
  <xsl:template match="p-is-empty-proof">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="signature"/>
    <trivial/>
  </xsl:template>

  <xsl:template match="r-is-empty-proof">
    <xsl:param name="signature"/>
    <trivial/>
  </xsl:template>

<!-- **************************************************************************************** 
     **  Transformation into a different type of obligation
     **************************************************************************************** -->
  <xsl:template match="etrs-to-reltrs-proof">  <!-- do nothing, transformation is implicit -->
    <xsl:param name="signature"/>
    <xsl:apply-templates mode="trs-noprooftag" select="../../proof-obligation">
      <xsl:with-param name="signature" select="$signature"/>
    </xsl:apply-templates>
  </xsl:template>


<!-- ****************************************************************************************
     ** Non-termination proofs
     **************************************************************************************** -->
  <xsl:template match="qtrs-nontermination-proof">
    <counter_example>
      <trs_counter_example>
        <start>
          <xsl:apply-templates mode="trs" select="loop/step[1]/term[1]"/>
        </start>
        <steps>
          <xsl:for-each select="loop/step">
            <step>
              <xsl:apply-templates select="."/>
            </step>
          </xsl:for-each>
        </steps>
        <xsl:apply-templates select="loop/position"/>
      </trs_counter_example>
    </counter_example>
  </xsl:template>
  
  <xsl:template match="reltrs-nontermination-proof">
    <counter_example>
      <trs_counter_example>
        <start>
          <xsl:apply-templates mode="trs" select="loop/relative-step[1]/descendant::step[1]/term[1]"/>
        </start>
        <steps>
          <xsl:for-each select="loop/relative-step[count(step) &gt; 0]">
            <step>
              <xsl:if test="count(s-steps) &gt; 0">
                <modulo>
                  <xsl:for-each select="s-steps/step">
                    <step>
                      <xsl:apply-templates select="."/>
                    </step>
                  </xsl:for-each>
                </modulo>
              </xsl:if>
              <xsl:apply-templates select="step"/>
            </step>
          </xsl:for-each>
        </steps>
        <xsl:for-each select="loop/relative-step[count(step) = 0]">
          <modulo>
            <xsl:for-each select="s-steps/step">
              <step>
                <xsl:apply-templates select="."/>
              </step>
            </xsl:for-each>
          </modulo>
        </xsl:for-each>
        <xsl:apply-templates select="loop/position"/>
      </trs_counter_example>
    </counter_example>
  </xsl:template>
  
  <xsl:template match="step">
    <xsl:apply-templates select="position"/>
    <xsl:apply-templates mode="trs" select="rule"/>
  </xsl:template>
  
  <xsl:template match="position">
    <position>
      <xsl:for-each select="integer">
        <arg><xsl:value-of select="@value - 1"/></arg>
      </xsl:for-each>
    </position>
  </xsl:template>
  
  
  <xsl:template match="qsrs-nontermination-proof">
    <!-- If the SRS was reversed before, we have to construct from this loop
         on the reversed system a loop over the original one.
         Note: We assume that an SRS is reversed at most once. -->
    <xsl:variable name="reversed">
      <xsl:choose>
        <xsl:when test="count(ancestor::proposition/proof/qtrs-reverse-proof) &gt; 0">1</xsl:when>
        <xsl:otherwise>0</xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <counter_example>
      <srs_counter_example>
        <start>
          <xsl:choose>
            <xsl:when test="$reversed = 1">
              <xsl:apply-templates mode="string_reverse" select="loop/step[1]/term[1]"/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:apply-templates mode="string" select="loop/step[1]/term[1]"/>
            </xsl:otherwise>
          </xsl:choose>
        </start>
        <steps>
          <xsl:for-each select="loop/step">
            <step>
              <xsl:apply-templates mode="string" select=".">
                <xsl:with-param name="reversed" select="$reversed"/>
              </xsl:apply-templates>
            </step>
          </xsl:for-each>
        </steps>
        <position>
          <xsl:choose>
            <xsl:when test="$reversed = 1">
              <xsl:variable name="startLength">
                <xsl:call-template name="stringLength">
                  <xsl:with-param name="string" select="loop/step[1]/term[1]"/>
                </xsl:call-template>
              </xsl:variable>
              <xsl:variable name="endLength">
                <xsl:call-template name="stringLength">
                  <xsl:with-param name="string" select="loop/step[count(../step)]/term[2]"/>
                </xsl:call-template>
              </xsl:variable>
              <xsl:value-of select="$endLength - $startLength - count(position/integer)"/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:value-of select="count(position/integer)"/>
            </xsl:otherwise>
          </xsl:choose>
        </position>
      </srs_counter_example>
    </counter_example>
  </xsl:template>
  
  <xsl:template match="relsrs-nontermination-proof">
    <xsl:variable name="reversed">
      <xsl:choose>
        <xsl:when test="count(ancestor::proposition/proof/reltrs-reverse-proof) &gt; 0">1</xsl:when>
        <xsl:otherwise>0</xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <counter_example>
      <srs_counter_example>
        <start>
          <xsl:choose>
            <xsl:when test="$reversed = 1">
              <xsl:apply-templates mode="string_reverse" select="loop/relative-step[1]/descendant::step[1]/term[1]"/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:apply-templates mode="string" select="loop/relative-step[1]/descendant::step[1]/term[1]"/>
            </xsl:otherwise>
          </xsl:choose>
        </start>
        <steps>
          <xsl:for-each select="loop/relative-step[count(step) &gt; 0]">
            <step>
              <xsl:if test="count(s-steps) &gt; 0">
                <modulo>
                  <xsl:for-each select="s-steps/step">
                    <step>
                      <xsl:apply-templates mode="string" select=".">
                        <xsl:with-param name="reversed" select="$reversed"/>
                      </xsl:apply-templates>
                    </step>
                  </xsl:for-each>
                </modulo>
              </xsl:if>
              <xsl:apply-templates mode="string" select="step">
                <xsl:with-param name="reversed" select="$reversed"/>
              </xsl:apply-templates>
            </step>
          </xsl:for-each>
        </steps>
        <xsl:for-each select="loop/relative-step[count(step) = 0]">
          <modulo>
            <xsl:for-each select="s-steps/step">
              <step>
                <xsl:apply-templates select="."/>
              </step>
            </xsl:for-each>
          </modulo>
        </xsl:for-each>
        <position>
          <xsl:choose>
            <xsl:when test="$reversed = 1">
              <xsl:variable name="startLength">
                <xsl:call-template name="stringLength">
                  <xsl:with-param name="string" select="loop/relative-step[1]/descendant::step[1]/term[1]"/>
                </xsl:call-template>
              </xsl:variable>
              <xsl:variable name="endLength">
                <xsl:call-template name="stringLength">
                  <xsl:with-param name="string" select="loop/relative-step[count(../relative-step)]/step[1]/term[2]"/>
                </xsl:call-template>
              </xsl:variable>
              <xsl:value-of select="$endLength - $startLength - count(position/integer)"/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:value-of select="count(position/integer)"/>
            </xsl:otherwise>
          </xsl:choose>
        </position>
      </srs_counter_example>
    </counter_example>
  </xsl:template>
  
  <xsl:template mode="string" match="step">
    <xsl:param name="reversed" select="0"/>
      <xsl:choose>
        <xsl:when test="$reversed = 1">
          <xsl:variable name="actTermLength">
            <xsl:call-template name="stringLength">
              <xsl:with-param name="string" select="term[1]"/>
            </xsl:call-template>
          </xsl:variable>
          <xsl:variable name="lhsLength">
            <xsl:call-template name="stringLength">
              <xsl:with-param name="string" select="rule/term[1]"/>
            </xsl:call-template>
          </xsl:variable>
          <position>
            <xsl:value-of select="$actTermLength - $lhsLength - count(position/integer)"/>
          </position>
          <xsl:apply-templates mode="string_reverse" select="rule"/>
        </xsl:when>
        <xsl:otherwise>
          <position>
            <xsl:value-of select="count(position/integer)"/>
          </position>
          <xsl:apply-templates mode="string" select="rule"/>
        </xsl:otherwise>
      </xsl:choose>
  </xsl:template>
  


<!-- **************************************************************************************** 
     **  Remove rules using an extended monotone algebra
     **  (no usable rules, no active, so we need just the order)
     **************************************************************************************** -->
  <xsl:template match="qtrs-rule-removal-proof">
    <xsl:param name="signature"/>
    <manna_ness>
      <xsl:apply-templates mode="for-qtrs" select="order">
        <xsl:with-param name="signature" select="$signature"/>
      </xsl:apply-templates>
      <xsl:apply-templates select="../../proof-obligation">
        <xsl:with-param name="signature" select="$signature"/>
      </xsl:apply-templates>
    </manna_ness>
  </xsl:template>
  
  <xsl:template match="reltrs-rule-removal-proof">
    <xsl:param name="signature"/>
    <manna_ness>
      <xsl:apply-templates mode="for-qtrs" select="order">
        <xsl:with-param name="signature" select="$signature"/>
      </xsl:apply-templates>
      <xsl:apply-templates select="../../proof-obligation">
        <xsl:with-param name="signature" select="$signature"/>
      </xsl:apply-templates>
    </manna_ness>
  </xsl:template>
  
<!-- **************************************************************************************** 
     **  Remove DPs by reduction pair
     **  (no usable rules, no active, so we need just the order)
     **************************************************************************************** -->
  <xsl:template match="qdp-reduction-pair-proof">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="signature"/>
    <manna_ness>
      <xsl:apply-templates mode="for-dps" select="order">    
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        <xsl:with-param name="signature" select="$signature"/>
      </xsl:apply-templates>
      <xsl:apply-templates select="../../proof-obligation">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        <xsl:with-param name="signature" select="$signature"/>
      </xsl:apply-templates>
    </manna_ness> 
  </xsl:template>


<!-- **************************************************************************************** 
     **  Output a polynomial order for use in combination with TRSs
     **************************************************************************************** -->
  <xsl:template mode="for-qtrs" match="polynomial-order">
    <xsl:param name="signature"/>
    <xsl:variable name="polo" select="."/>
    <order>
    <poly_int>
    <xsl:for-each select="exslt:node-set($signature)/signature/symbol">
      <xsl:variable name="ar" select="@arity"/>
      <xsl:variable name="na" select="@name"/>
      <mapping>
        <fun><xsl:value-of select="$na"/></fun>
        <xsl:choose>
	      <xsl:when test="count($polo/polo-interpretation/symbol[@name = $na and @arity = $ar]) = 0">
	         <!-- not a known value, so create entry with default interpretation -->
	         <!-- <polynomial/> -->
	         <xsl:call-template name="dummy-pol">
	           <xsl:with-param name="arity" select="$ar"/>
	         </xsl:call-template>
	      </xsl:when>
	      <xsl:otherwise>
	         <!-- take the lookup-value -->
	        <xsl:apply-templates select="$polo/polo-interpretation/symbol[@name = $na and @arity = $ar]/../polynomial">
      	      <xsl:with-param name="arity" select="$ar"/>
            </xsl:apply-templates>
	      </xsl:otherwise>
	    </xsl:choose>
      </mapping>
    </xsl:for-each>
    </poly_int>
    </order>
  </xsl:template>

<!-- **************************************************************************************** 
     **  Output a polynomial order for use in combination with DPs 
     **  (Rainbow demands interpretations for all symbols of original system and for all
     **   tuple-symbols (even for constructors). This is the reason for a special "for-dps"-mode
     **   where tuple-symbols are generated.
     **  Params: tuple-symbols is the map from defined-to-tuple-symbols
     **          signature is the signature of the original TRS (root-node in whole proof)
     **************************************************************************************** -->
  <xsl:template mode="for-dps" match="polynomial-order">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="signature"/>
    <xsl:variable name="polo" select="."/>
    <order>
    <poly_int>
    <!-- loop over signature, since we need to give interpretations for all symbols of signature! -->
    <xsl:for-each select="exslt:node-set($signature)/signature/symbol">
      <xsl:variable name="ar" select="@arity"/>
      <xsl:variable name="na" select="@name"/>

      <!-- first the tupled version -->
      <mapping>
      <fun><hd_mark><xsl:value-of select="$na"/></hd_mark></fun>
      <xsl:choose>
        <xsl:when test="count(exslt:node-set($tuple-symbols)/defined-to-tuple/entry/orig/symbol[@name = $na and @arity = $ar]) = 0">
           <!-- not a defined symbol that has a tuple-symbol, so create one with default interpretation -->
           <polynomial/>
        </xsl:when>
        <xsl:otherwise>
           <!-- we have already created a tuple-symbol, but it is not clear that we have an interpretation -->
                <xsl:variable name="tsym" select="exslt:node-set($tuple-symbols)/defined-to-tuple/entry/orig/symbol[@name = $na and @arity = $ar]/../../tupled/symbol"/>
                <xsl:variable name="tna" select="$tsym/@name"/>
	      <xsl:choose>
	        <xsl:when test="count($polo/polo-interpretation/symbol[@name = $tna and @arity = $ar]) = 0">
	           <!-- not a known value for tuple-symbol, so create one with default interpretation -->
	           <polynomial/>
	        </xsl:when>
	        <xsl:otherwise>
	           <!-- just lookup the value -->
	          <xsl:apply-templates select="$polo/polo-interpretation/symbol[@name = $tna and @arity = $ar]/../polynomial">
        	             <xsl:with-param name="arity" select="$ar"/>
                    </xsl:apply-templates>
	        </xsl:otherwise>    
	      </xsl:choose>
        </xsl:otherwise>    
      </xsl:choose>
      </mapping>


  <!-- second: consider original symbols -->
  <!-- problem: if say, rule removal has been applied as first proof step before generating DPs,
        then some may have vanished completely and 
        afterwards f may be the name of some tuple-symbol. In that case we should interpret
        f by 0 and not by pol(f)!
      This has not been tested properly! 
   -->
      <mapping>
      <fun><int_mark><xsl:value-of select="$na"/></int_mark></fun>
      <xsl:choose>
         <xsl:when test="count(exslt:node-set($tuple-symbols)/defined-to-tuple/entry/tupled/symbol[@name = $na and @arity = $ar]) != 0">
           <!-- symbol is tuple-symbol, so case in description applies -->
           <polynomial/>
         </xsl:when>
         <xsl:otherwise>
            <!-- try lookup in map -->
	      <xsl:choose>
	        <xsl:when test="count($polo/polo-interpretation/symbol[@name = $na and @arity = $ar]) = 0">
	           <!-- not a known value, so create entry with default interpretation -->
	           <polynomial/>
	        </xsl:when>
	        <xsl:otherwise>
	           <!-- take the lookup-value -->
	          <xsl:apply-templates select="$polo/polo-interpretation/symbol[@name = $na and @arity = $ar]/../polynomial">
        	             <xsl:with-param name="arity" select="$ar"/>
                    </xsl:apply-templates>
	        </xsl:otherwise>
	      </xsl:choose>
         </xsl:otherwise>
       </xsl:choose>
      </mapping>
    </xsl:for-each>  
    </poly_int>
    </order>
  </xsl:template>


<!-- **************************************************************************************** 
     **  Output a matrix order for use in combination with TRSs
     **************************************************************************************** -->
  <xsl:template mode="for-qtrs" match="matrix-order">
  <xsl:param name="signature"/>
  <xsl:variable name="matro" select="matrix-interpretation"/>
  <order>
    <xsl:choose> <!-- determine tag -->
      <xsl:when test="@type = 'int'">
        <matrix_int>
          <dimension><xsl:value-of select="@dimension"/></dimension>
          <xsl:call-template name="rrr-matro-interpretations">
            <xsl:with-param name="signature" select="$signature"/>
            <xsl:with-param name="matro" select="$matro"/>
          </xsl:call-template>
        </matrix_int>
      </xsl:when>
      <xsl:when test="@type = 'arctic'">
        <xsl:choose>
          <xsl:when test="@belowZero = 'true'">
            <arctic_bz_int>
              <dimension><xsl:value-of select="@dimension"/></dimension>
              <xsl:call-template name="rrr-matro-interpretations">
                <xsl:with-param name="signature" select="$signature"/>
                <xsl:with-param name="matro" select="$matro"/>
              </xsl:call-template>
            </arctic_bz_int>
          </xsl:when>
          <xsl:otherwise>
            <arctic_int>
              <dimension><xsl:value-of select="@dimension"/></dimension>
              <xsl:call-template name="rrr-matro-interpretations">
                <xsl:with-param name="signature" select="$signature"/>
                <xsl:with-param name="matro" select="$matro"/>
              </xsl:call-template>
            </arctic_int>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
      <xsl:otherwise>Error: Unsupported type supplied for matrix-order!</xsl:otherwise>
    </xsl:choose>
  </order>
  </xsl:template>
  
  <xsl:template name="rrr-matro-interpretations">
  <xsl:param name="signature"/>
  <xsl:param name="matro"/>
    <xsl:variable name="type" select="$matro/../@type"/>
    <xsl:variable name="dimension" select="$matro/../@dimension"/>
    <mi_map>
    <xsl:for-each select="exslt:node-set($signature)/signature/symbol">
      <xsl:variable name="ar" select="@arity"/>
      <xsl:variable name="na" select="@name"/>
      <mapping>
        <fun><xsl:value-of select="$na"/></fun>
        <xsl:choose>
          <xsl:when test="count($matro//symbol[@name = $na and @arity = $ar]) = 0">
          <!-- not a known value, so create entry with default interpretation -->
            <xsl:call-template name="default-interpretation">
              <xsl:with-param name="type" select="$type"/>
	          <xsl:with-param name="dimension" select="$dimension"/>
              <xsl:with-param name="arity" select="$ar"/>
            </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <mi_fun>
            <!-- take the lookup-value -->
              <xsl:apply-templates select="$matro//symbol[@name = $na and @arity = $ar]/../mpolynomial"/>
            </mi_fun>
          </xsl:otherwise>
        </xsl:choose>
      </mapping>
    </xsl:for-each> 
    </mi_map>
  </xsl:template>

<!-- **************************************************************************************** 
     **  Output a matrix order for use in combination with DPs
     **************************************************************************************** -->
  <xsl:template mode="for-dps" match="matrix-order">
  <xsl:param name="tuple-symbols"/>
  <xsl:param name="signature"/>
  <xsl:variable name="matro" select="matrix-interpretation"/>
  <order>
    <xsl:choose> <!-- determine tag -->
      <xsl:when test="@type = 'int'">
        <matrix_int>
          <dimension><xsl:value-of select="@dimension"/></dimension>
          <xsl:call-template name="matro-interpretations">
            <xsl:with-param name="signature" select="$signature"/>
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
            <xsl:with-param name="matro" select="$matro"/>
          </xsl:call-template>
        </matrix_int>
      </xsl:when>
      <xsl:when test="@type = 'arctic'">
        <xsl:choose>
          <xsl:when test="@belowZero = 'true'">
            <arctic_bz_int>
              <dimension><xsl:value-of select="@dimension"/></dimension>
              <xsl:call-template name="matro-interpretations">
                <xsl:with-param name="signature" select="$signature"/>
                <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
                <xsl:with-param name="matro" select="$matro"/>
              </xsl:call-template>
            </arctic_bz_int>
          </xsl:when>
          <xsl:otherwise>
            <arctic_int>
              <dimension><xsl:value-of select="@dimension"/></dimension>
              <xsl:call-template name="matro-interpretations">
                <xsl:with-param name="signature" select="$signature"/>
                <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
                <xsl:with-param name="matro" select="$matro"/>
              </xsl:call-template>
            </arctic_int>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
      <xsl:otherwise>Error: Unsupported type supplied for matrix-order!</xsl:otherwise>
    </xsl:choose>
  </order>
  </xsl:template>
  
  <xsl:template name="matro-interpretations">
  <xsl:param name="tuple-symbols"/>
  <xsl:param name="signature"/>
  <xsl:param name="matro"/>
    <xsl:variable name="type" select="$matro/../@type"/>
    <xsl:variable name="dimension" select="$matro/../@dimension"/>
    <mi_map>
    <xsl:for-each select="exslt:node-set($signature)/signature/symbol">
      <xsl:variable name="ar" select="@arity"/>
      <xsl:variable name="na" select="@name"/>

      <!-- first the tupled version -->
      <mapping>
        <fun><hd_mark><xsl:value-of select="$na"/></hd_mark></fun>
        <xsl:choose>
          <xsl:when test="count(exslt:node-set($tuple-symbols)/defined-to-tuple/entry/orig/symbol[@name = $na and @arity = $ar]) = 0">
            <!-- not a defined symbol that has a tuple-symbol, so create one with default interpretation -->
            <xsl:call-template name="default-interpretation">
	          <xsl:with-param name="type" select="$type"/>
	          <xsl:with-param name="dimension" select="$dimension"/>
	          <xsl:with-param name="arity" select="$ar"/>
	        </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <!-- we have already created a tuple-symbol, but it is not clear that we have an interpretation -->
            <xsl:variable name="tsym" select="exslt:node-set($tuple-symbols)/defined-to-tuple/entry/orig/symbol[@name = $na and @arity = $ar]/../../tupled/symbol"/>
            <xsl:variable name="tna" select="$tsym/@name"/>
	        <xsl:choose>
              <xsl:when test="count($matro//symbol[@name = $tna and @arity = $ar]) = 0">
	            <!-- not a known value for tuple-symbol, so create one with default interpretation -->
	            <xsl:call-template name="default-interpretation">
	              <xsl:with-param name="type" select="$type"/>
	              <xsl:with-param name="dimension" select="$dimension"/>
	              <xsl:with-param name="arity" select="$ar"/>
	            </xsl:call-template>
	          </xsl:when>
	          <xsl:otherwise>
	            <!-- just lookup the value -->
	            <mi_fun>
	              <xsl:apply-templates select="$matro//symbol[@name = $tna and @arity = $ar]/../mpolynomial" />
                </mi_fun>
              </xsl:otherwise>    
	        </xsl:choose>
          </xsl:otherwise>    
        </xsl:choose>
      </mapping>


      <!-- second: consider original symbols -->
      <!-- problem: if say, rule removal has been applied as first proof step before generating DPs,
           then some may have vanished completely and afterwards f may be the name of some tuple-symbol.
           In that case we should interpret f by 0 and not by pol(f)!
           This has not been tested properly! 
      -->
      <mapping>
        <fun><int_mark><xsl:value-of select="$na"/></int_mark></fun>
        <xsl:choose>
          <xsl:when test="count(exslt:node-set($tuple-symbols)/defined-to-tuple/entry/tupled/symbol[@name = $na and @arity = $ar]) != 0">
            <!-- symbol is tuple-symbol, so case in description applies -->
            <xsl:call-template name="default-interpretation">
	          <xsl:with-param name="type" select="$type"/>
	          <xsl:with-param name="dimension" select="$dimension"/>
	          <xsl:with-param name="arity" select="$ar"/>
	        </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <!-- try lookup in map -->
	        <xsl:choose>
	          <xsl:when test="count($matro//symbol[@name = $na and @arity = $ar]) = 0">
	            <!-- not a known value, so create entry with default interpretation -->
	            <xsl:call-template name="default-interpretation">
	              <xsl:with-param name="type" select="$type"/>
	              <xsl:with-param name="dimension" select="$dimension"/>
	              <xsl:with-param name="arity" select="$ar"/>
	            </xsl:call-template>
	          </xsl:when>
              <xsl:otherwise>
                <mi_fun>
	              <!-- take the lookup-value -->
	              <xsl:apply-templates select="$matro//symbol[@name = $na and @arity = $ar]/../mpolynomial"/>
	            </mi_fun>
	          </xsl:otherwise>
            </xsl:choose>
          </xsl:otherwise>
        </xsl:choose>
      </mapping>
    </xsl:for-each> 
    </mi_map>
  </xsl:template>
  
  <xsl:template match="mpolynomial">
    <!-- the first child must be the constant part, according to Rainbow's grammar --> 
    <const>
      <xsl:for-each select="mmonomial[count(polo-factor) = 0]/matrix/mvect/*">
      <velem>
        <xsl:apply-templates select="."/>
      </velem>
      </xsl:for-each>
    </const>
    <xsl:for-each select="mmonomial[count(polo-factor) > 0]">
    <arg>
      <xsl:apply-templates select="matrix"/>
    </arg>
    </xsl:for-each>
  </xsl:template>
  
  <!-- vectors are rows in Rainbow, not columns, so we must transpose our matrices -->  
  <xsl:template match="matrix">
    <xsl:for-each select="mvect[1]/*">
      <xsl:variable name="pos" select="position()"/>
      <row>
        <xsl:for-each select="../../mvect/*[position() = $pos]">
          <velem>
            <xsl:apply-templates select="."/>
          </velem>
        </xsl:for-each>
      </row>
    </xsl:for-each>
  </xsl:template>
  
  <!-- Default interpretations -->
  <!-- Note: This implementation uses [1, 0, ..., 0] for the constant vector. This ensures
       that all interpretations, including those of 0-ary symbols, are absolute positive.
       However, if we ever want to use arctic matrices with RRR (which is correct for SRSs,
       but not currently supported by CoLoR), then we have to change this because there,
       the constant vector has to be [0, ..., 0]. --> 
  <xsl:template name="default-interpretation">
  <xsl:param name="type"/>
  <xsl:param name="arity"/>
  <xsl:param name="dimension"/>
    <mi_fun>
      <const>
        <xsl:call-template name="ithUnityVector">
          <xsl:with-param name="type" select="$type"/>
          <xsl:with-param name="length" select="$dimension"/>
          <xsl:with-param name="i" select="1"/>
          <xsl:with-param name="j" select="1"/>
        </xsl:call-template>
      </const>
      <xsl:for-each select="1 to $arity">
        <arg>
          <xsl:call-template name="buildUnityMatrix">
            <xsl:with-param name="type" select="$type"/>
            <xsl:with-param name="dimension" select="$dimension"/>
            <xsl:with-param name="i" select="1"/>
          </xsl:call-template>
        </arg>
      </xsl:for-each>
    </mi_fun>
  </xsl:template>
  
  <xsl:template name="buildUnityMatrix">
  <xsl:param name="type"/>
  <xsl:param name="dimension"/>
  <xsl:param name="i"/>
    <row>
      <xsl:call-template name="ithUnityVector">
        <xsl:with-param name="type" select="$type"/>
        <xsl:with-param name="length" select="$dimension"/>
        <xsl:with-param name="i" select="$i"/>
        <xsl:with-param name="j" select="1"/>
      </xsl:call-template>
    </row>
    <xsl:if test="$i &lt; $dimension">
      <xsl:call-template name="buildUnityMatrix">
        <xsl:with-param name="type" select="$type"/>
        <xsl:with-param name="dimension" select="$dimension"/>
        <xsl:with-param name="i" select="$i + 1"/>
      </xsl:call-template>
    </xsl:if>
  </xsl:template>
  
  <xsl:template name="ithUnityVector">
  <xsl:param name="type"/>
  <xsl:param name="length"/>
  <xsl:param name="i"/>
  <xsl:param name="j"/>
    <velem>
      <xsl:choose>
        <xsl:when test="$i = $j">
          <xsl:call-template name="oneElement">
            <xsl:with-param name="type" select="$type"/>
          </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
          <xsl:call-template name="zeroElement">
            <xsl:with-param name="type" select="$type"/>
          </xsl:call-template>
        </xsl:otherwise>
      </xsl:choose>
    </velem>
    <xsl:if test="$j &lt; $length">
      <xsl:call-template name="ithUnityVector">
        <xsl:with-param name="type" select="$type"/>
        <xsl:with-param name="length" select="$length"/>
        <xsl:with-param name="i" select="$i"/>
        <xsl:with-param name="j" select="$j + 1"/>
      </xsl:call-template>
    </xsl:if>
  </xsl:template>
  
  <xsl:template name="zeroElement">
  <xsl:param name="type"/>
    <xsl:choose>
      <xsl:when test="$type = 'arctic'">
        <minus_infinite/>
      </xsl:when>
      <xsl:otherwise>
        0
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template name="oneElement">
  <xsl:param name="type"/>
    <xsl:choose>
      <xsl:when test="$type = 'arctic'">
        <finite>0</finite>
      </xsl:when>
      <xsl:otherwise>
        1
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>


<!-- **************************************************************************************** 
     **  Polynomials
     **  (important to know: polys are used in context of a symbol f (Pol(f) = poly).
     **                      and the arity of f has to be passed as argument, since 
     **                      Rainbow-representation of polys rely on this arity!)
     **************************************************************************************** -->

  <xsl:template name="dummy-pol">
    <xsl:param name="arity"/>
    <xsl:variable name="i" select="1"/>
    <polynomial>
      <xsl:call-template name="dummy-mon">
        <xsl:with-param name="arity" select="$arity"/>
        <xsl:with-param name="index" select="1"/>
      </xsl:call-template>
    </polynomial>
  </xsl:template>
  
  <xsl:template name="dummy-mon">
    <xsl:param name="arity"/>
    <xsl:param name="index"/>
    <xsl:if test="$arity + 1 &gt; $index">
      <monomial>
        <coef>1</coef>
        <xsl:call-template name="dummy-vars">
          <xsl:with-param name="arity" select="$arity"/>
          <xsl:with-param name="var" select="$index"/>
          <xsl:with-param name="index" select="1"/>
        </xsl:call-template>
      </monomial>
      <xsl:call-template name="dummy-mon">
        <xsl:with-param name="arity" select="$arity"/>
        <xsl:with-param name="index" select="$index + 1"/>
      </xsl:call-template>
    </xsl:if>
  </xsl:template>
  
  <xsl:template name="dummy-vars">
    <xsl:param name="arity"/>
    <xsl:param name="var"/>
    <xsl:param name="index"/>
    <xsl:if test="$arity + 1 &gt; $index">
      <xsl:choose>
        <xsl:when test="$var = $index">
          <var>1</var>
        </xsl:when>
        <xsl:otherwise>
          <var>0</var>
        </xsl:otherwise>
      </xsl:choose>
      <xsl:call-template name="dummy-vars">
        <xsl:with-param name="arity" select="$arity"/>
        <xsl:with-param name="var" select="$var"/>
        <xsl:with-param name="index" select="$index + 1"/>
      </xsl:call-template>
    </xsl:if>
  </xsl:template>
  
  <xsl:template match="polynomial">
    <xsl:param name="arity"/>
    <polynomial>
        <xsl:for-each select="monomial">
          <xsl:apply-templates select=".">
            <xsl:with-param name="arity" select="$arity"/>
          </xsl:apply-templates>
        </xsl:for-each>
    </polynomial>
  </xsl:template>

  <!-- first output coef then the list of all variables with factors -->
  <xsl:template match="monomial">
    <xsl:param name="arity"/>
      <monomial>
      <coef><xsl:apply-templates select="integer"/></coef>
       <xsl:apply-templates mode="loop" select=".">
          <xsl:with-param name="arity" select="$arity"/>
          <xsl:with-param name="i" select="1"/>
       </xsl:apply-templates>
      </monomial>
  </xsl:template>

  <!-- iteration over all possible variables, cf. Rainbow format -->
  <xsl:template mode="loop" match="monomial">
    <xsl:param name="arity"/>
    <xsl:param name="i"/>
    <xsl:if test="$i &lt;= $arity">
        <xsl:variable name="xi" select="concat('x_',$i)"/>
        <!-- check whether xi occurs in this monomial -->
        <xsl:choose>
          <xsl:when test="count(polo-factor/variable[@name = $xi]) = 0">
            <!-- if not, then add xi^0 as factor. This has to be done for Rainbow format -->
             <var>0</var>
          </xsl:when>
          <xsl:otherwise>
            <!-- otherwise add xi^n as factor -->
             <var><xsl:apply-templates select="polo-factor/variable[@name = $xi]/../integer"/></var>
          </xsl:otherwise>
        </xsl:choose>
       <xsl:apply-templates mode="loop" select=".">
          <xsl:with-param name="arity" select="$arity"/>
          <xsl:with-param name="i" select="$i+1"/>
       </xsl:apply-templates>
    </xsl:if>
  </xsl:template>





<!-- **************************************************************************************** 
     **   Term related data-structures      
     **   There are two difficulties in this part:
     **   - variable-names in rules have to be generated from 0 to n                 
     **   - for symbols we have to do some lookup in tuple-symbol table
     **************************************************************************************** -->


<!-- symbol - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -->
<!-- needs parameter tuple-symbols
      for non-tuple-symbol f: generates <int_mark>f</int_mark>
      for tuple-symbol F: generates <hd_mark>f</hd_mark> where f is the original symbol for F
   -->
  <xsl:template match="symbol">
    <xsl:param name="tuple-symbols"/>
    <xsl:variable name="ar" select="@arity"/>
    <xsl:variable name="na" select="@name"/>
    <xsl:choose>
      <!-- use exslt:node-set to query generated node of tuple-symbols -->
      <xsl:when test="count(exslt:node-set($tuple-symbols)/defined-to-tuple/entry/tupled/symbol[@name = $na and @arity = $ar]) = 0"> 
        <fun><int_mark><xsl:value-of select="$na"/></int_mark></fun>
      </xsl:when>
      <xsl:otherwise>
        <fun><hd_mark><xsl:value-of select="exslt:node-set($tuple-symbols)/defined-to-tuple/entry/tupled/symbol[@name = $na and @arity = $ar]/../../orig/symbol/@name"/></hd_mark></fun>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>


<!-- term: x - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -->
  <xsl:template match="variable">
    <xsl:param name="varmap"/>
    <xsl:variable name="na" select="@name"/>
    <var><xsl:value-of select="exslt:node-set($varmap)/mapping/entry[@name = $na]/@number"/></var>
  </xsl:template>

<!-- term: f(t_1,..,t_n) - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -->
  <xsl:template match="fun-app">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="varmap"/>
    <app>
      <xsl:apply-templates select="symbol">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
      <xsl:for-each select="term">
        <arg>
          <xsl:apply-templates select=".">
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
            <xsl:with-param name="varmap" select="$varmap"/>
          </xsl:apply-templates>
        </arg>
      </xsl:for-each>
    </app>
  </xsl:template>

  
<!-- rule - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -->
  
  <!-- gen_var_map performs left-to-right traversal to build variable-mapping.
       this is done instead of selecting .//variable to guarantee left-to-right numbering
       (I am unsure whether .//variable has reliable order of variables)
  -->
  <xsl:template mode="gen_var_map" match="fun-app">
    <xsl:param name="varmap"/>
    <xsl:apply-templates mode="gen_var_map_arg" select=".">
      <xsl:with-param name="varmap" select="$varmap"/>
      <xsl:with-param name="i" select="1"/>
    </xsl:apply-templates>
  </xsl:template>

  <xsl:template mode="gen_var_map_arg" match="fun-app">
    <xsl:param name="varmap"/>
    <xsl:param name="i"/>
    <xsl:choose>
      <xsl:when test="$i &lt;= count(term)">
        <xsl:apply-templates mode="gen_var_map_arg" select=".">
          <xsl:with-param name="i" select="1+$i"/>          
          <xsl:with-param name="varmap">
            <xsl:apply-templates mode="gen_var_map" select="term[$i]">
              <xsl:with-param name="varmap" select="$varmap"/>
            </xsl:apply-templates>
          </xsl:with-param>
        </xsl:apply-templates>
      </xsl:when>
      <xsl:otherwise>
        <xsl:copy-of select="$varmap"/>              
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template mode="gen_var_map" match="variable">
    <xsl:param name="varmap"/>
    <xsl:variable name="na" select="@name"/>
    <xsl:choose>
      <xsl:when test="count(exslt:node-set($varmap)/mapping/entry[@name = $na]) = 0">
        <!-- new variable -->
        <mapping>
          <xsl:for-each select="exslt:node-set($varmap)/mapping/entry">
            <xsl:copy-of select="."/>
          </xsl:for-each>
          <xsl:element name="entry">
            <xsl:attribute name="name">
              <xsl:value-of select="$na"/>
            </xsl:attribute>
            <xsl:attribute name="number">
              <xsl:value-of select="count(exslt:node-set($varmap)/mapping/entry)"/>
            </xsl:attribute>
          </xsl:element>
        </mapping>
      </xsl:when>
      <xsl:otherwise>
        <!-- already known variable -->
        <!-- to make sure the numbering is correct, add a "dummy" element to the map,
        	 with no name (so it will never be fetched). --> 
        <mapping>
          <xsl:for-each select="exslt:node-set($varmap)/mapping/entry">
            <xsl:copy-of select="."/>
          </xsl:for-each>
          <xsl:element name="entry">
            <xsl:attribute name="name">
            </xsl:attribute>
            <xsl:attribute name="number">
              <xsl:value-of select="count(exslt:node-set($varmap)/mapping/entry)"/>
            </xsl:attribute>
          </xsl:element>
        </mapping>    
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- outputs a rule where the variable-mapping from names to numbers is provided -->
  <xsl:template mode="output" match="rule">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="varmap"/>
    <rule>
      <lhs>
        <xsl:apply-templates select="term[1]">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          <xsl:with-param name="varmap" select="$varmap"/>
        </xsl:apply-templates>
      </lhs>
      <rhs>
        <xsl:apply-templates select="term[2]">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          <xsl:with-param name="varmap" select="$varmap"/>
        </xsl:apply-templates>
      </rhs>
    </rule>
  </xsl:template>

  <!-- rules are first variable renamed (by the index of their first occurrence)
       before generating xml-code. This only has to be done for rainbow
       => as soon as rainbow can handle names, this code has to be updated
  -->  
  <xsl:template match="rule">
    <xsl:param name="tuple-symbols"/>
    <xsl:apply-templates mode="output" select=".">
      <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      <xsl:with-param name="varmap">
        <!-- in this part, the variable mapping is generated -->
        <xsl:apply-templates mode="gen_var_map" select="term[2]">
          <xsl:with-param name="varmap">
            <xsl:apply-templates mode="gen_var_map" select="term[1]">
              <xsl:with-param name="varmap"><mapping/></xsl:with-param>
            </xsl:apply-templates>
          </xsl:with-param>
        </xsl:apply-templates>
      </xsl:with-param>
    </xsl:apply-templates>
  </xsl:template>


<!-- Terms and rules w/o tuple symbols -->

  <xsl:template mode="trs" match="symbol">
    <fun><xsl:value-of select="@name"/></fun>
  </xsl:template>
  
  <xsl:template mode="trs" match="term">
    <xsl:param name="varmap">
      <xsl:apply-templates mode="gen_var_map" select=".">
        <xsl:with-param name="varmap"><mapping/></xsl:with-param>
      </xsl:apply-templates>
    </xsl:param>
    <xsl:apply-templates mode="trs_with-varmap">
      <xsl:with-param name="varmap" select="$varmap"/>
    </xsl:apply-templates>
  </xsl:template>
  
  <xsl:template mode="trs_with-varmap" match="variable">
    <xsl:param name="varmap"/>
    <xsl:variable name="na" select="@name"/>
    <var><xsl:value-of select="exslt:node-set($varmap)/mapping/entry[@name = $na]/@number"/></var>
  </xsl:template>

  <xsl:template mode="trs_with-varmap" match="fun-app">
    <xsl:param name="varmap"/>
    <app>
      <xsl:apply-templates mode="trs" select="symbol"/>
      <xsl:for-each select="term">
        <arg>
          <xsl:apply-templates mode="trs" select=".">
            <xsl:with-param name="varmap" select="$varmap"/>
          </xsl:apply-templates>
        </arg>
      </xsl:for-each>
    </app>
  </xsl:template>
  
  <xsl:template mode="trs_output" match="rule">
    <xsl:param name="varmap"/>
    <rule>
      <lhs>
        <xsl:apply-templates mode="trs_with-varmap" select="term[1]">
          <xsl:with-param name="varmap" select="$varmap"/>
        </xsl:apply-templates>
      </lhs>
      <rhs>
        <xsl:apply-templates mode="trs_with-varmap" select="term[2]">
          <xsl:with-param name="varmap" select="$varmap"/>
        </xsl:apply-templates>
      </rhs>
    </rule>
  </xsl:template>
  
  <xsl:template mode="trs" match="rule">
    <xsl:apply-templates mode="trs_output" select=".">
      <xsl:with-param name="varmap">
        <!-- in this part, the variable mapping is generated -->
        <xsl:apply-templates mode="gen_var_map" select="term[2]">
          <xsl:with-param name="varmap">
            <xsl:apply-templates mode="gen_var_map" select="term[1]">
              <xsl:with-param name="varmap"><mapping/></xsl:with-param>
            </xsl:apply-templates>
          </xsl:with-param>
        </xsl:apply-templates>
      </xsl:with-param>
    </xsl:apply-templates>
  </xsl:template>
  
  <!-- Terms as strings. Make sure to only apply this template to proper strings
       (i.e., terms containing only unary symbols). This is not checked. -->
  <xsl:template mode="string" match="term">
    <xsl:apply-templates mode="string"/>
  </xsl:template>
  
  <xsl:template mode="string" match="fun-app">
    <letter>
      <xsl:value-of select="symbol/@name"/>
    </letter>
    <xsl:apply-templates mode="string" select="term[1]"/>
  </xsl:template>
  
  <xsl:template mode="string" match="rule">
    <rule>
      <lhs>
        <xsl:apply-templates mode="string" select="term[1]"/>
      </lhs>
      <rhs>
        <xsl:apply-templates mode="string" select="term[2]"/>
      </rhs>
    </rule>
  </xsl:template>
  
  
  <xsl:template mode="string_reverse" match="term">
    <xsl:apply-templates mode="string_reverse"/>
  </xsl:template>
  
  <xsl:template mode="string_reverse" match="fun-app">
    <xsl:apply-templates mode="string_reverse" select="term[1]"/>
    <letter>
      <xsl:value-of select="symbol/@name"/>
    </letter>
  </xsl:template>
  
  <xsl:template mode="string_reverse" match="rule">
    <rule>
      <lhs>
        <xsl:apply-templates mode="string_reverse" select="term[1]"/>
      </lhs>
      <rhs>
        <xsl:apply-templates mode="string_reverse" select="term[2]"/>
      </rhs>
    </rule>
  </xsl:template>
  
  
  <xsl:template name="stringLength">
    <xsl:param name="string"/>
    <xsl:value-of select="count($string/descendant-or-self::symbol)"/>
  </xsl:template>
  

<!-- **************************************************************************************** 
     **  Extract the signature of a TRS 
     **  (set of symbols, if signature is not already provided)
     **************************************************************************************** -->
  <!--
  <xsl:template mode="sig_extract" match="qtrs">
     <xsl:choose>
       <xsl:when test="count(signature) = 1">
         <xsl:copy-of select="signature"/>
       </xsl:when>
       <xsl:otherwise>
          <xsl:apply-templates mode="sig_gen" select=".">
            <xsl:with-param name="i" select="1"/>
            <xsl:with-param name="sig">
              <signature/>
            </xsl:with-param>
          </xsl:apply-templates>
       </xsl:otherwise>
     </xsl:choose>
  </xsl:template>
  -->
  <xsl:template mode="sig_gen" match="basic-obligation">
    <xsl:param name="sig"/>
    <xsl:param name="i"/>
    <xsl:choose>
      <!-- the above choose is a loop over all symbols -->
      <!-- the case below states that we have one more symbol to visit -->
       <xsl:when test="count(./*[1]//symbol) &gt;= $i">
           <xsl:variable name="sym" select="(./*[1]//symbol)[$i]"/>
           <xsl:variable name="ar" select="$sym/@arity"/>
           <xsl:variable name="na" select="$sym/@name"/>
           <xsl:choose>
             <!-- is it a new symbol, then extend the signature -->
             <xsl:when test="count(exslt:node-set($sig)/signature/symbol[@name = $na and @arity = $ar]) = 0"> 
               <xsl:apply-templates mode="sig_gen" select=".">
                  <xsl:with-param name="i" select="$i + 1"/>
                  <xsl:with-param name="sig">
	           <signature>
		    <xsl:for-each select="exslt:node-set($sig)/signature/symbol">
                      <xsl:copy-of select="."/>
                    </xsl:for-each>
                    <xsl:copy-of select="$sym"/>
	           </signature>
                  </xsl:with-param>
               </xsl:apply-templates>
	         </xsl:when>
             <xsl:otherwise>
               <xsl:apply-templates mode="sig_gen" select=".">
                  <xsl:with-param name="i" select="$i + 1"/>
                  <xsl:with-param name="sig" select="$sig"/>
               </xsl:apply-templates>
             </xsl:otherwise>
            </xsl:choose>
        </xsl:when>
        <xsl:otherwise>
          <xsl:copy-of select="$sig"/>
        </xsl:otherwise>
     </xsl:choose>
  </xsl:template>
  
  <xsl:template name="sig_extract">
    <!-- select whether given signature should be used or whether it should be generated -->
     <xsl:choose>
       <xsl:when test="count(./*[1]//signature) = 1">
         <xsl:copy-of select="./*[1]//signature"/>
       </xsl:when>
       <xsl:otherwise>
          <xsl:apply-templates mode="sig_gen" select=".">
            <xsl:with-param name="i" select="1"/>
            <xsl:with-param name="sig">
              <signature/>
            </xsl:with-param>
          </xsl:apply-templates>
       </xsl:otherwise>
     </xsl:choose>
  </xsl:template>


  <!-- *********** various ********* -->

  <xsl:template match="integer"><xsl:value-of select="@value"/></xsl:template>
  
  <xsl:template match="arctic-int">
    <xsl:choose>
      <xsl:when test="@infinite = 'true'"><minus_infinite/></xsl:when>
      <xsl:otherwise><finite><xsl:value-of select="@value"/></finite></xsl:otherwise>
    </xsl:choose>
  </xsl:template>

</xsl:transform>
