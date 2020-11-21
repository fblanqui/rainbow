<?xml version="1.0" encoding="iso-8859-1"?>

<!-- Transforms XML proofs from AProVE into the certification problem format.
-->

<!-- author: ckuknat -->

<xsl:transform xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
               xmlns:exslt="http://exslt.org/common"
               exclude-result-prefixes="exslt"
               version="2.0">

  <xsl:output method="xml"/>


  <!-- Starting point -->

  <xsl:template match="/">
    <certificationProblem>
      <goal>
        <xsl:choose>
          <xsl:when test="count(//qtrs-nontermination-proof) &gt; 0">
        	<nonTermination/>
          </xsl:when>
          <xsl:when test="count(//qsrs-nontermination-proof) &gt; 0">
        	<nonTermination/>
          </xsl:when>
          <xsl:when test="count(//reltrs-nontermination-proof) &gt; 0">
        	<nonTermination/>
          </xsl:when>
          <xsl:when test="count(//relsrs-nontermination-proof) &gt; 0">
        	<nonTermination/>
          </xsl:when>
          <xsl:otherwise>
            <termination/>
          </xsl:otherwise>
        </xsl:choose>
      </goal>
      <input>
        <trsInput>
          <xsl:choose>
            <xsl:when test="count(proof-obligation/proposition/basic-obligation/reltrs-termination-obligation) &gt; 0">
              <trs>
                <xsl:apply-templates mode="nosharp" select="/proof-obligation/proposition/basic-obligation/reltrs-termination-obligation/reltrs/trs[1]"/>
              </trs>
              <relativeRules>
                <rules>
                  <xsl:call-template name="ruleset-nosharp">
                    <xsl:with-param name="rules" select="/proof-obligation/proposition/basic-obligation/reltrs-termination-obligation/reltrs/trs[2]"/>
                  </xsl:call-template>
                </rules>
              </relativeRules>            
            </xsl:when>
            <xsl:otherwise>
              <trs>
                <xsl:apply-templates mode="nosharp" select="/proof-obligation/proposition/basic-obligation/qtrs-termination-obligation/qtrs/trs"/>
              </trs>
            </xsl:otherwise>
          </xsl:choose>
        </trsInput>
      </input>
      <proof>
        <xsl:choose>
          <xsl:when test="count(//qtrs-nontermination-proof) &gt; 0">
            <xsl:apply-templates mode="nonTerm" select="/proof-obligation/proposition/proof"/>
          </xsl:when>
          <xsl:when test="count(//qsrs-nontermination-proof) &gt; 0">
            <xsl:apply-templates mode="nonTerm" select="/proof-obligation/proposition/proof"/>
          </xsl:when>
          <xsl:when test="count(//reltrs-nontermination-proof) &gt; 0">
            <xsl:apply-templates mode="nonTerm" select="/proof-obligation/proposition/proof"/>
          </xsl:when>
          <xsl:when test="count(//relsrs-nontermination-proof) &gt; 0">
            <xsl:apply-templates mode="nonTerm" select="/proof-obligation/proposition/proof"/>
          </xsl:when>
          <xsl:otherwise>
            <xsl:apply-templates mode="trs" select="/proof-obligation/proposition/proof"/>
          </xsl:otherwise>
        </xsl:choose>
      </proof>
      <origin>
        <proofOrigin>
          <!-- proof origin -->
        </proofOrigin>
        <inputOrigin>
          <!-- input origin -->
        </inputOrigin>
      </origin>
    </certificationProblem>
  </xsl:template>

  <!-- *************************************************************************
       ***                            Proofs                                 ***
       *************************************************************************
-->

  <!-- After DPTrans, the variable $tuple-symbols has to be carried everywhere.
       Before DPTrans, it doesn't exist, so we need two types of proofs for these
       situations. We start with mode="trs", and the DPTrans proof automatically
       switches it off.
-->

  <xsl:template mode="trs" match="proof">
    <xsl:apply-templates mode="trs"/>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="proof">
    <xsl:apply-templates mode="nonTerm"/>
  </xsl:template>

  <xsl:template match="proof">
    <xsl:param name="tuple-symbols"/>
    <xsl:apply-templates>
      <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
    </xsl:apply-templates>
  </xsl:template>


  <!-- 
-->
  <!-- *************************************************************************
       ***  Dependency pair transformation.                                  ***
       ***  Create $tuple-symbols variable and pass it to subsequent proofs, ***
       ***  switch trs mode off.                                             ***
       *************************************************************************-->

  <xsl:template mode="trs" match="qtrs-dependency-pairs-proof">
    <xsl:variable name="tuple-symbols">
      <defined-to-tuple>
      <!-- we add some more structure with orig/tuple, than just using symbol[1/2]
-->
        <xsl:for-each select="defined-to-tuple-entry">
          <entry>
            <orig><xsl:copy-of select="symbol[1]"/></orig>
            <tupled><xsl:copy-of select="symbol[2]"/></tupled>
          </entry>
        </xsl:for-each>
      </defined-to-tuple>
    </xsl:variable>
    <dpTrans>
      <xsl:variable name="origPairs">
        <xsl:for-each select="rule-to-dps-entry">
          <xsl:for-each select="position-to-dp">
            <xsl:copy-of select="rule"/>
          </xsl:for-each>
        </xsl:for-each>
      </xsl:variable>
      <dps>
        <rules>
          <xsl:call-template name="ruleset">
            <xsl:with-param name="rules" select="$origPairs"/>
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          </xsl:call-template>
        </rules>
      </dps>
      <markedSymbols>
        <xsl:text>true</xsl:text>
      </markedSymbols>
      <xsl:apply-templates select="../../proof-obligation/proposition/proof">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
    </dpTrans>
  </xsl:template>
  
  <!-- *************************************************************************
       ***                   srs-as-trs-proof                               ***
       *************************************************************************-->
  
  <xsl:template mode="trs" match="srs-as-trs-proof">
    <xsl:apply-templates mode="trs" select="../../proof-obligation/proposition/proof"/>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="srs-as-trs-proof">
    <xsl:apply-templates mode="nonTerm" select="../../proof-obligation/proposition/proof"/>
  </xsl:template>
  
  <!-- *************************************************************************
       ***                   srs-reverse-proof                               ***
       *************************************************************************-->
  
  <xsl:template mode="trs" match="qtrs-reverse-proof">
    <stringReversal>
      <trs>
        <xsl:apply-templates mode="nosharp" select="trs"/>
      </trs>
      <xsl:apply-templates mode="trs" select="../../proof-obligation/proposition/proof"/>
    </stringReversal>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="qtrs-reverse-proof">
    <trs>
      <xsl:apply-templates mode="nosharp" select="trs"/>
    </trs>
    <stringReversal>
      <xsl:apply-templates mode="nonTerm" select="../../proof-obligation/proposition/proof"/>
    </stringReversal>
  </xsl:template>
  
  <xsl:template mode="trs" match="reltrs-reverse-proof">
    <trs>
      <xsl:apply-templates mode="nosharp" select="trs"/>
    </trs>
    <stringReversal>
      <xsl:apply-templates mode="trs" select="../../proof-obligation/proposition/proof"/>
    </stringReversal>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="reltrs-reverse-proof">
    <trs>
      <xsl:apply-templates mode="nosharp" select="trs"/>
    </trs>
    <srsReversal>
      <xsl:apply-templates mode="nonTerm" select="../../proof-obligation/proposition/proof"/>
    </srsReversal>
  </xsl:template>

  <!-- *************************************************************************
       ***                   Non- termination- proof                        ***
       *************************************************************************-->

  <xsl:template mode="nonTerm" match="qtrs-nontermination-proof">
    <xsl:choose>
      <xsl:when test="count(loop)=0">
        <variableConditionViolated/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates mode="trs"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="reltrs-nontermination-proof">
    <xsl:choose>
      <xsl:when test="count(loop)=0">
        <variableConditionViolated/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates mode="reltrs"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- don't know yet what happens to steps with reltrs's -->
  <xsl:template mode="reltrs" match="loop">
    <loop>
      <xsl:apply-templates mode="reltrs" select="relative-step"/>
      <xsl:apply-templates mode="trs" select="substitution"/>
      <xsl:apply-templates mode="trs" select="context"/>
    </loop>
  </xsl:template>
  
  <xsl:template mode="reltrs" match="relative-step">
    <xsl:apply-templates mode="reltrs" select="s-steps"/>
    <xsl:apply-templates mode="trs" select="step"/>    
  </xsl:template>
  
  <xsl:template mode="reltrs" match="s-steps">
    <xsl:apply-templates mode="reltrs" select="step"/>    
  </xsl:template>
  
  <xsl:template mode="reltrs" match="step">
    <redex type="rel">
      <xsl:apply-templates mode="nosharp" select="term[1]"/>
      <positionInTerm>
        <xsl:if test="count(position/integer) &gt; 0">
          <xsl:call-template name="positionList">
            <xsl:with-param name="node" select="position"/>
            <xsl:with-param name="stop" select="count(position/integer)"/>
          </xsl:call-template>
        </xsl:if>
      </positionInTerm>
      <xsl:apply-templates mode="nosharp" select="rule"/>
    </redex>
  </xsl:template>
  
  <xsl:template mode="trs" match="loop">
    <loop>
      <xsl:apply-templates mode="trs" select="step"/>
      <xsl:apply-templates mode="trs" select="substitution"/>
      <xsl:apply-templates mode="trs" select="context"/>
    </loop>
  </xsl:template>

  <xsl:template mode="trs" match="step">
    <redex>
      <xsl:apply-templates mode="nosharp" select="term[1]"/>
      <positionInTerm>
        <xsl:if test="count(position/integer) &gt; 0">
          <xsl:call-template name="positionList">
            <xsl:with-param name="node" select="position"/>
            <xsl:with-param name="stop" select="count(position/integer)"/>
          </xsl:call-template>
        </xsl:if>
      </positionInTerm>
      <xsl:apply-templates mode="nosharp" select="rule"/>
    </redex>
  </xsl:template>

  <xsl:template name="positionList">
    <xsl:param name="node"/>
    <xsl:param name="start" select="1"/>
    <xsl:param name="stop" select="count($node/integer)"/>
    <xsl:choose>
      <xsl:when test="$start &gt; $stop">
        <xsl:text/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:if test="count($node/integer) &gt; 0">
          <position>
            <xsl:value-of select="$node/integer[$start]/@value"/>
          </position>
        </xsl:if>
        <xsl:call-template name="positionList">
          <xsl:with-param name="node" select="$node"/>
          <xsl:with-param name="start" select="$start+1"/>
          <xsl:with-param name="stop" select="$stop"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- Converts a list of <term> elements that are found below a common parent.
       Params: $parent - parent element of the terms; $start - index of the first
       term to be included in the output; $stop - dito for the last term
-->
  <xsl:template name="termList">
    <xsl:param name="parent"/>
    <xsl:param name="start" select="1"/>
    <xsl:param name="stop" select="count($parent/term)"/>
    <xsl:choose>
      <xsl:when test="$start &gt; $stop">
        <xsl:text/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates mode="nosharp" select="$parent/term[$start]"/>
      </xsl:otherwise>
    </xsl:choose>
    <xsl:choose>
      <xsl:when test="$start &lt; $stop">
        <xsl:call-template name="termList">
          <xsl:with-param name="parent" select="$parent"/>
          <xsl:with-param name="start" select="$start + 1"/>
          <xsl:with-param name="stop" select="$stop"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- context = Hole | More symbol term* subcontext term* -->
  <xsl:template mode="trs" match="context">
    <xsl:choose>
      <xsl:when test="count(symbol) = 0">
        <box/>
      </xsl:when>
      <xsl:otherwise>
        <funContext>
	      <xsl:apply-templates mode="nosharp" select="./symbol"/>
          <xsl:variable name="numLeftTerms">
            <xsl:call-template name="countLeftTerms"/>
          </xsl:variable>
          <before>
            <xsl:choose>
	          <xsl:when test="$numLeftTerms = 0">
	            <xsl:text/>
	          </xsl:when>
	          <xsl:otherwise>
	            <xsl:call-template name="termList">
	              <xsl:with-param name="parent" select="."/>
	              <xsl:with-param name="stop" select="$numLeftTerms"/>
	            </xsl:call-template>
	          </xsl:otherwise>
	        </xsl:choose>
	      </before>
          <xsl:apply-templates mode="trs" select="context"/>
          <after>
            <xsl:choose>
	          <xsl:when test="count(labeledSymbol) = 0">
	            <xsl:choose>
                  <xsl:when test="$numLeftTerms = symbol/@arity - count(context/box)">
	                <xsl:text/>
	              </xsl:when>
	              <xsl:otherwise>
	                <xsl:call-template name="termList">
	                  <xsl:with-param name="parent" select="."/>
	                  <xsl:with-param name="start" select="$numLeftTerms + 1"/>
	                </xsl:call-template>
                  </xsl:otherwise>
                </xsl:choose>
	          </xsl:when>
	          <xsl:otherwise>
	            <xsl:choose>
                  <xsl:when test="$numLeftTerms = labeledSymbol/symbol/@arity - count(context/box)">
	                <xsl:text/>
	              </xsl:when>
	              <xsl:otherwise>
	                <xsl:call-template name="termList">
	                  <xsl:with-param name="parent" select="."/>
	                  <xsl:with-param name="start" select="$numLeftTerms + 1"/>
	                </xsl:call-template>
                  </xsl:otherwise>
                </xsl:choose>
	          </xsl:otherwise>
	        </xsl:choose>
	      </after>
        </funContext>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- context = Hole | More symbol term* subcontext term* -->
  <!-- create a context in non-trs-mode due to context in
       flatContext after dpTrans -->
  <xsl:template match="context">
    <xsl:param name="tuple-symbols"/>
    <xsl:choose>
      <xsl:when test="count(symbol) = 0">
        <box/>
      </xsl:when>
      <xsl:otherwise>
        <funContext>
	      <xsl:apply-templates select="./symbol">
	        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
	      </xsl:apply-templates>
          <xsl:variable name="numLeftTerms">
            <xsl:call-template name="countLeftTerms"/>
          </xsl:variable>
          <before>
            <xsl:choose>
	          <xsl:when test="$numLeftTerms = 0">
	            <xsl:text/>
	          </xsl:when>
	          <xsl:otherwise>
	            <xsl:call-template name="termList">
	              <xsl:with-param name="parent" select="."/>
	              <xsl:with-param name="stop" select="$numLeftTerms"/>
	            </xsl:call-template>
	          </xsl:otherwise>
	        </xsl:choose>
	      </before>
          <xsl:apply-templates select="context"/>
          <after>
            <xsl:choose>
              <xsl:when test="count(labeledSymbol) = 0">
  	            <xsl:choose>
	              <xsl:when test="$numLeftTerms = symbol/@arity - count(context/box)">
	                <xsl:text/>
	              </xsl:when>
	              <xsl:otherwise>
	                <xsl:call-template name="termList">
	                  <xsl:with-param name="parent" select="."/>
	                  <xsl:with-param name="start" select="$numLeftTerms + 1"/>
	                </xsl:call-template>
	              </xsl:otherwise>
	            </xsl:choose>
	          </xsl:when>
	          <xsl:otherwise>
	            <xsl:choose>
	              <xsl:when test="$numLeftTerms = labeledSymbol/symbol/@arity - count(context/box)">
	                <xsl:text/>
	              </xsl:when>
	              <xsl:otherwise>
	                <xsl:call-template name="termList">
	                  <xsl:with-param name="parent" select="."/>
	                  <xsl:with-param name="start" select="$numLeftTerms + 1"/>
	                </xsl:call-template>
	              </xsl:otherwise>
	            </xsl:choose>
	          </xsl:otherwise>
	        </xsl:choose>
	      </after>
        </funContext>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- Determines the number of <term> children in the current <context> element that come before
       the sub-<context>.
       Apparently, there is no easier way in XSLT to compute this.
-->
  <xsl:template name="countLeftTerms">
    <xsl:param name="i" select="1"/>
    <xsl:param name="total" select="0"/>
    <xsl:choose>
      <xsl:when test="*[$i]/local-name() = 'context'">
        <xsl:number value="$total"/>
      </xsl:when>
      <xsl:when test="*[$i]/local-name() = 'term'">
        <xsl:call-template name="countLeftTerms">
          <xsl:with-param name="i" select="$i+1"/>
          <xsl:with-param name="total" select="$total + 1"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="countLeftTerms">
          <xsl:with-param name="i" select="$i+1"/>
          <xsl:with-param name="total" select="$total"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template mode="trs" match="substitution">
    <substitution>
      <xsl:choose>
        <xsl:when test="count(substitute) &gt; 0">
          <xsl:call-template name="substitutes">
            <xsl:with-param name="parent" select="."/>
          </xsl:call-template>
        </xsl:when>
        <!-- No substitutions which could be generated -->
        <xsl:otherwise><xsl:text/></xsl:otherwise>
      </xsl:choose>
    </substitution>
  </xsl:template>

  <xsl:template name="substitutes">
    <xsl:param name="parent"/>
    <xsl:param name="i" select="1"/>
    <substEntry>
      <xsl:apply-templates mode="nosharp" select="$parent/substitute[$i]/variable"/>
      <xsl:apply-templates mode="nosharp" select="$parent/substitute[$i]/term"/>
    </substEntry>
    <xsl:choose>
      <xsl:when test="$i &lt; count($parent/substitute)">
	    <xsl:call-template name="substitutes">
	      <xsl:with-param name="parent" select="$parent"/>
	      <xsl:with-param name="i" select="$i + 1"/>
	    </xsl:call-template>
      </xsl:when>
      <!-- No more substitutes left -->
      <xsl:otherwise><xsl:text/></xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- ****************************************************************************************
       **  R-is-empty proof
       **************************************************************************************** -->

  <xsl:template mode="trs" match="r-is-empty-proof">
    <xsl:param name="tuple-symbols"/>
    <rIsEmpty/>
  </xsl:template>

  <!-- ****************************************************************************************
       **  P-is-empty proof
       **************************************************************************************** -->

  <xsl:template match="p-is-empty-proof">
    <xsl:param name="tuple-symbols"/>
    <pIsEmpty/>
  </xsl:template>

  <!-- ****************************************************************************************
       **  Semantic Labeling
       **************************************************************************************** -->

  <xsl:template mode="trs" match="qtrs-semantic-labeling-proof">
    <semlab>
      <finiteModel>
        <carrierSize>
          <xsl:apply-templates select="integer"/>
        </carrierSize>
        <!-- TODO pointWise etc.??? -->
      </finiteModel>
      <trs>
        <xsl:apply-templates mode="nosharp" select="trs"/>
      </trs>
      <xsl:apply-templates mode="trs" select="../../proof-obligation/proposition/proof"/>
    </semlab>
  </xsl:template>

  <xsl:template match="qdp-semantic-labeling-proof">
    <semlabProc>
      <finiteModel>
        <carrierSize>
          <xsl:apply-templates select="integer"/>
        </carrierSize>
        <!-- TODO pointWise etc.??? -->
      </finiteModel>
      <trs>
        <xsl:apply-templates mode="nosharp" select="trs[1]"/>
      </trs>
      <trs>
        <xsl:apply-templates mode="nosharp" select="trs[2]"/>
      </trs>
      <xsl:apply-templates select="../../proof-obligation/proposition/proof"/>
    </semlabProc>
  </xsl:template>

  <!-- ****************************************************************************************
       **  Root Labeling
       **************************************************************************************** -->

  <xsl:template mode="trs" match="qtrs-root-labeling-proof">
    <semlab>
      <model>
        <rootLabeling/>
      </model>
      <trs>
        <xsl:apply-templates mode="nosharp" select="trs"/>
      </trs>
      <xsl:apply-templates mode="trs" select="../../proof-obligation/proposition/proof"/>
    </semlab>
  </xsl:template>

  <!-- ****************************************************************************************
       **  Flat Context Closure
       **************************************************************************************** -->

  <xsl:template mode="trs" match="qtrs-flat-cc-proof">
    <flatContextClosure>
      <flatContexts>
        <xsl:apply-templates mode="trs" select="flat-context/context"/>
      </flatContexts>
      <trs>
        <xsl:apply-templates mode="nosharp" select="trs"/>
      </trs>
      <xsl:apply-templates mode="trs" select="../../proof-obligation/proposition/proof"/>
    </flatContextClosure>
  </xsl:template>

  <xsl:template match="qtrs-flat-cc-proof">
    <xsl:param name="tuple-symbols"/>
    <flatContextClosureProc>
      <flatContexts>
        <xsl:apply-templates select="flat-context/context"/>
      </flatContexts>
      <dps>
        <rules>
          <xsl:apply-templates select="../proposition/basic-obligation/qdp-termination-obligation/qdp/dps/rule">
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          </xsl:apply-templates>
        </rules>
      </dps>
      <trs>
        <xsl:apply-templates select="trs">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        </xsl:apply-templates>
      </trs>
      <xsl:apply-templates select="../../proof-obligation/proposition/proof">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
    </flatContextClosureProc>
  </xsl:template>

  <!-- ****************************************************************************************
       **  Path Order
       **************************************************************************************** -->

  <xsl:template match="path-order">
    <xsl:param name="countAfs" select="count(afs)"/>
    <xsl:param name="tuple-symbols"/>
    <pathOrder>
      <statusPrecedence>
        <xsl:apply-templates select="statusMap/status">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        </xsl:apply-templates>
      </statusPrecedence>
      <xsl:if test="$countAfs>0">
        <xsl:apply-templates select="afs">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        </xsl:apply-templates>
      </xsl:if>
    </pathOrder>
  </xsl:template>

  <xsl:template match="status">
    <xsl:param name="tuple-symbols"/>
    <statusPrecedenceEntry>
      <xsl:apply-templates select="symbol">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
      <arity>
        <xsl:choose>
          <xsl:when test="count(labeledSymbol) = 0">
            <xsl:value-of select="symbol/@arity"/>
          </xsl:when>
          <xsl:otherwise>
            <xsl:value-of select="labeledSymbol/symbol/@arity"/>
          </xsl:otherwise>
        </xsl:choose>
      </arity>
      <precedence>
        <xsl:value-of select="prec/integer/@value"/>
      </precedence>
      <xsl:choose>
        <xsl:when test="count(lex) > 0"><lex/></xsl:when>
        <xsl:otherwise><mul/></xsl:otherwise>
      </xsl:choose>
    </statusPrecedenceEntry>
  </xsl:template>

  <xsl:template mode="for-dps" match="afs">
    <xsl:param name="tuple-symbols"/>
    <xsl:variable name="path" select="."/>
    <arg_filter_proj>
      <def>
   	    <xsl:apply-templates select="filter">
   	      <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        </xsl:apply-templates>
   	  </def>
   	  <proof>
        <xsl:apply-templates mode="for-dps" select="../../path-order">
          <xsl:with-param name="countAfs" select="0"/>
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        </xsl:apply-templates>
      </proof>
   	</arg_filter_proj>
  </xsl:template>

  <xsl:template match="filter">
    <xsl:param name="tuple-symbols" />
	<mapping>
	  <xsl:apply-templates select="symbol">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
	  <xsl:choose>
        <xsl:when test="@collapse = 'true'">
          <proj>
            <xsl:value-of select="collapse/integer/@value"/>
          </proj>
        </xsl:when>
        <xsl:otherwise>
          <filter>
            <xsl:apply-templates select="boolean"/>
          </filter>
        </xsl:otherwise>
      </xsl:choose>
    </mapping>
  </xsl:template>

  <xsl:template match="boolean">
    <xsl:choose>
    <xsl:when test="@value='true'">
      <xsl:text>true</xsl:text>
    </xsl:when>
    <xsl:otherwise>
      <xsl:text>false</xsl:text>
    </xsl:otherwise>
  </xsl:choose>
  </xsl:template>

  <!-- RPO for mode trs -->

  <xsl:template mode="trs" match="path-order">
    <xsl:param name="countAfs" select="count(afs)"/>
    <pathOrder>
      <statusPrecedence>
        <xsl:apply-templates mode="trs" select="statusMap/status"/>
      </statusPrecedence>
      <xsl:if test="$countAfs>0">
        <xsl:apply-templates mode="trs" select="afs"/>
      </xsl:if>
    </pathOrder>
  </xsl:template>

  <xsl:template mode="trs" match="status">
    <statusPrecedenceEntry>
      <xsl:apply-templates mode="trs" select="symbol"/>
      <arity>
        <xsl:choose>
          <xsl:when test="count(labeledSymbol) = 0">
            <xsl:value-of select="symbol/@arity"/>
          </xsl:when>
          <xsl:otherwise>
            <xsl:value-of select="labeledSymbol/symbol/@arity"/>
          </xsl:otherwise>
        </xsl:choose>
      </arity>
      <precedence>
        <xsl:value-of select="prec/integer/@value"/>
      </precedence>
      <xsl:choose>
        <xsl:when test="count(lex) > 0"><lex/></xsl:when>
        <xsl:otherwise><mul/></xsl:otherwise>
      </xsl:choose>
    </statusPrecedenceEntry>
  </xsl:template>

  <xsl:template mode="for-qtrs" match="afs">
    <xsl:variable name="path" select="."/>
    <arg_filter_proj>
      <def>
   	    <xsl:apply-templates mode="trs" select="filter"/>
   	  </def>
   	  <proof>
        <xsl:apply-templates mode="for-qtrs" select="../../path-order">
          <xsl:with-param name="countAfs" select="0"/>
        </xsl:apply-templates>
      </proof>
   	</arg_filter_proj>
  </xsl:template>

  <xsl:template mode="trs" match="filter">
	<mapping>
	  <xsl:apply-templates mode="trs" select="symbol"/>
	  <xsl:choose>
        <xsl:when test="@collapse = 'true'">
          <proj>
            <xsl:value-of select="collapse/integer/@value"/>
          </proj>
        </xsl:when>
        <xsl:otherwise>
          <filter>
            <xsl:apply-templates mode="trs" select="boolean"/>
          </filter>
        </xsl:otherwise>
      </xsl:choose>
    </mapping>
  </xsl:template>

  <xsl:template mode="trs" match="boolean">
    <xsl:choose>
    <xsl:when test="@value='true'">
      <xsl:text>true</xsl:text>
    </xsl:when>
    <xsl:otherwise>
      <xsl:text>false</xsl:text>
    </xsl:otherwise>
  </xsl:choose>
  </xsl:template>

  <!-- ****************************************************************************************
       **  Dependency graph proof
       **************************************************************************************** -->

  <xsl:template match="qdp-dependency-graph-proof">
    <xsl:param name="tuple-symbols"/>
    <depGraphProc>
      <xsl:choose>
        <xsl:when test="count(graph-scc) = 0">
          <xsl:text/>
        </xsl:when>
        <xsl:when test="count(graph-scc) = 1">
          <xsl:call-template name="scc">
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
            <xsl:with-param name="sccProposition" select="../../proof-obligation/proposition"/>
            <xsl:with-param name="graph-scc" select="graph-scc"/>
          </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
          <xsl:call-template name="sccList">
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
            <xsl:with-param name="proofTag" select="."/>
          </xsl:call-template>
        </xsl:otherwise>
      </xsl:choose>
    </depGraphProc>
  </xsl:template>

  <xsl:template name="scc">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="sccProposition"/>
    <xsl:param name="graph-scc"/>
    <component>
      <dps>
        <rules>
          <xsl:apply-templates select="$sccProposition/basic-obligation/qdp-termination-obligation/qdp/dps/rule">
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          </xsl:apply-templates>
        </rules>
      </dps>
      <xsl:choose>
        <xsl:when test="count($sccProposition/proof/non-scc) = 0">
          <realScc>
            <xsl:text>true</xsl:text>
          </realScc>
          <xsl:if test="count($graph-scc/identifier) &gt; 0">
            <xsl:call-template name="forwardArcs">
              <xsl:with-param name="scc" select="$graph-scc"/>
              <xsl:with-param name="index" select="1"/>
            </xsl:call-template>
          </xsl:if>
          <xsl:apply-templates select="$sccProposition/proof">
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          </xsl:apply-templates>
        </xsl:when>
        <xsl:otherwise>
          <realScc>
            <xsl:text>false</xsl:text>
          </realScc>
          <xsl:if test="count($graph-scc/identifier) &gt; 0">
            <xsl:call-template name="forwardArcs">
              <xsl:with-param name="scc" select="$graph-scc"/>
              <xsl:with-param name="index" select="1"/>
            </xsl:call-template>
          </xsl:if>
        </xsl:otherwise>
      </xsl:choose>
    </component>
  </xsl:template>
  
  <xsl:template name="forwardArcs">
    <xsl:param name="scc"/>
    <xsl:param name="index" select="1"/>
    <forwardArc>
      <xsl:value-of select="$scc/identifier[$index]/@name"/>
    </forwardArc>
    <xsl:if test="count($scc/identifier) &gt; $index">
      <xsl:call-template name="forwardArcs">
        <xsl:with-param name="scc" select="$scc"/>
        <xsl:with-param name="index" select="$index + 1"/>
      </xsl:call-template>
    </xsl:if>
  </xsl:template>

  <!-- if the scc's have to be in an order other way round 
  <xsl:template name="sccList">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="proofTag"/>
    <xsl:param name="i" select="1"/>
    <xsl:call-template name="scc">
      <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      <xsl:with-param name="sccProposition" select="$proofTag/../../proof-obligation/conjunction/proof-obligation[$i]/proposition"/>
      <xsl:with-param name="graph-scc" select="$proofTag/graph-scc[$i]"/>
    </xsl:call-template>
    <xsl:choose>
      <xsl:when test="$i &lt; count($proofTag/../../proof-obligation/conjunction/proof-obligation)">
        <xsl:call-template name="sccList">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          <xsl:with-param name="proofTag" select="$proofTag"/>
          <xsl:with-param name="i" select="$i + 1"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  -->

  <xsl:template name="sccList">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="proofTag"/>
    <xsl:param name="i" select="count($proofTag/../../proof-obligation/conjunction/proof-obligation)"/>
    <xsl:call-template name="scc">
      <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      <xsl:with-param name="sccProposition" select="$proofTag/../../proof-obligation/conjunction/proof-obligation[$i]/proposition"/>
      <xsl:with-param name="graph-scc" select="$proofTag/graph-scc[$i]"/>
    </xsl:call-template>
    <xsl:choose>
      <xsl:when test="$i &gt; 1">
        <xsl:call-template name="sccList">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          <xsl:with-param name="proofTag" select="$proofTag"/>
          <xsl:with-param name="i" select="$i - 1"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- ****************************************************************************************
       **  Reduction pair proof
       **************************************************************************************** -->

  <xsl:template match="qdp-reduction-pair-proof">
    <xsl:param name="tuple-symbols"/>
    <xsl:choose>
      <!-- Test if the set of usable rules is equal to the set of the qdp -->
      <xsl:when test="count(trs[1]/rule) &lt; count(../../basic-obligation/qdp-termination-obligation/qdp/trs/rule)">
        <redPairUrProc>
          <redPair>
            <xsl:apply-templates select="order">
              <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
            </xsl:apply-templates>
          </redPair>
          <dps>
            <xsl:apply-templates select="trs[3]">
              <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
            </xsl:apply-templates>
          </dps>
          <usableRules>
            <xsl:apply-templates select="trs[1]">
              <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
            </xsl:apply-templates>
          </usableRules>
          <xsl:apply-templates select="../../proof-obligation/proposition/proof">
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          </xsl:apply-templates>
        </redPairUrProc>
      </xsl:when>
      <xsl:otherwise>
        <redPairProc>
          <redPair>
            <xsl:apply-templates select="order">
              <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
            </xsl:apply-templates>
          </redPair>
          <dps>
            <xsl:apply-templates select="trs[3]">
              <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
            </xsl:apply-templates>
          </dps>
          <xsl:apply-templates select="../../proof-obligation/proposition/proof">
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          </xsl:apply-templates>
        </redPairProc>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- ****************************************************************************************
       **  Rule removal proof
       **************************************************************************************** -->

  <xsl:template mode="trs" match="qtrs-rule-removal-proof">
    <ruleRemoval>
      <redPair>
        <xsl:apply-templates mode="nosharp" select="order"/>
      </redPair>
      <trs>
        <!-- trs[2] are the REMAINING rules, that CPF wants to have -->
        <xsl:apply-templates mode="nosharp" select="trs[2]"/>
      </trs>
      <xsl:apply-templates mode="trs" select="../../proof-obligation/proposition/proof"/>
    </ruleRemoval>
  </xsl:template>
  
  <xsl:template mode="trs" match="reltrs-rule-removal-proof">
    <ruleRemoval>
      <redPair>
        <xsl:apply-templates mode="nosharp" select="order"/>
      </redPair>
      <trs>
        <!-- trs[2] are the REMAINING rules, that CPF wants to have -->
        <xsl:apply-templates mode="nosharp" select="trs[2]"/>
      </trs>
      <xsl:apply-templates mode="trs" select="../../proof-obligation/proposition/proof"/>
    </ruleRemoval>
  </xsl:template>
  
  <!-- If we do not terminate: ignore deleted rules in later loops so we can skip ruleRemoval -->
  
  <xsl:template mode="nonTerm" match="qtrs-rule-removal-proof">
    <xsl:apply-templates mode="nonTerm" select="../../proof-obligation/proposition/proof"/>
  </xsl:template>
  
  <xsl:template mode="nonTerm" match="reltrs-rule-removal-proof">
    <xsl:apply-templates mode="nonTerm" select="../../proof-obligation/proposition/proof"/>
  </xsl:template>

  <!-- ****************************************************************************************
       **  Orders
       **************************************************************************************** -->

  <xsl:template match="order">
    <xsl:param name="tuple-symbols"/>
    <xsl:apply-templates>
      <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
    </xsl:apply-templates>
  </xsl:template>

  <xsl:template mode="nosharp" match="order">
    <xsl:apply-templates mode="nosharp"/>
  </xsl:template>

  <!-- ****************************************************************************************
       **  Polynomial Order
       **************************************************************************************** -->

  <xsl:template match="polynomial-order">
    <xsl:param name="tuple-symbols"/>
    <interpretation>
      <type>
        <polynomial>
          <domain>
            <naturals/>
          </domain>
          <degree>
            <xsl:text>1</xsl:text>
          </degree>
        </polynomial>
      </type>
      <xsl:call-template name="polo-mappings">
        <xsl:with-param name="order" select="."/>
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:call-template>
    </interpretation>
  </xsl:template>

  <xsl:template mode="nosharp" match="polynomial-order">
    <interpretation>
      <type>
        <polynomial>
          <domain>
            <naturals/>
          </domain>
          <degree>
            <xsl:text>1</xsl:text>
          </degree>
        </polynomial>
      </type>
      <xsl:call-template name="polo-mappings-nosharp">
        <xsl:with-param name="order" select="."/>
      </xsl:call-template>
    </interpretation>
  </xsl:template>

  <xsl:template name="polo-mappings">
    <xsl:param name="order"/>
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="i" select="1"/>
    <xsl:apply-templates select="$order/polo-interpretation[$i]">
      <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
    </xsl:apply-templates>
    <xsl:choose>
      <xsl:when test="$i &lt; count($order/polo-interpretation)">
        <xsl:call-template name="polo-mappings">
          <xsl:with-param name="order" select="$order"/>
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          <xsl:with-param name="i" select="$i + 1"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="polo-mappings-nosharp">
    <xsl:param name="order"/>
    <xsl:param name="i" select="1"/>
    <xsl:apply-templates mode="nosharp" select="$order/polo-interpretation[$i]"/>
    <xsl:choose>
      <xsl:when test="$i &lt; count($order/polo-interpretation)">
        <xsl:call-template name="polo-mappings-nosharp">
          <xsl:with-param name="order" select="$order"/>
          <xsl:with-param name="i" select="$i + 1"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="polo-interpretation">
    <xsl:param name="tuple-symbols"/>
    <interpret>
      <xsl:apply-templates select="symbol">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
      <xsl:apply-templates select="labeledSymbol">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
      <xsl:apply-templates select="polynomial"/>
    </interpret>
  </xsl:template>

  <xsl:template mode="nosharp" match="polo-interpretation">
    <interpret>
      <xsl:apply-templates mode="nosharp" select="symbol"/>
      <xsl:apply-templates mode="nosharp" select="labeledSymbol"/>
      <xsl:apply-templates select="polynomial"/>
    </interpret>
  </xsl:template>

  <xsl:template match="polynomial">
    <arity>
      <xsl:choose>
        <xsl:when test="count(../labeledSymbol) = 0">
          <xsl:value-of select="../symbol/@arity"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="../labeledSymbol/symbol/@arity"/>
        </xsl:otherwise>
      </xsl:choose>
    </arity>
    <polynomial>
      <sum>
        <xsl:choose>
          <xsl:when test="count(monomial)=0">
            <polynomial>
              <coefficient>
                <integer>0</integer>
              </coefficient>
            </polynomial>
          </xsl:when>
          <xsl:otherwise>
            <xsl:apply-templates select="monomial"/>
          </xsl:otherwise>
        </xsl:choose>
      </sum>
    </polynomial>
  </xsl:template>

  <xsl:template match="monomial">
    <polynomial>
      <xsl:choose>
        <xsl:when test="count(polo-factor) = 0">
          <coefficient>
            <integer>
              <xsl:value-of select="integer/@value"/>
            </integer>
          </coefficient>
        </xsl:when>
        <xsl:otherwise>
          <product>
            <polynomial>
              <coefficient>
                <integer>
                  <xsl:value-of select="integer/@value"/>
                </integer>
              </coefficient>
            </polynomial>
            <xsl:if test="count(polo-factor) &gt; 0">
              <xsl:call-template name="polo-factors">
                <xsl:with-param name="monom" select="."/>
              </xsl:call-template>
            </xsl:if>
          </product>
        </xsl:otherwise>
      </xsl:choose>
    </polynomial>
  </xsl:template>

  <xsl:template name="polo-factors">
    <xsl:param name="monom"/>
    <xsl:param name="factorIndex" select="1"/>
    <xsl:call-template name="factor">
      <xsl:with-param name="var" select="$monom/polo-factor[$factorIndex]/variable"/>
    </xsl:call-template>
    <xsl:if test="count($monom/polo-factor) &gt; $factorIndex">
      <xsl:call-template name="polo-factors">
        <xsl:with-param name="monom" select="."/>
        <xsl:with-param name="factorIndex" select="$factorIndex + 1"/>
      </xsl:call-template>
    </xsl:if>
  </xsl:template>
  
  <xsl:template name="factor">
    <xsl:param name="var"/>
    <xsl:param name="index" select="1"/>
    <xsl:choose>
      <xsl:when test="concat('x_', $index) = $var/@name">
        <xsl:call-template name="variable">
          <xsl:with-param name="iteration" select="$var/../integer/@value"/>
          <xsl:with-param name="index" select="$index"/>
        </xsl:call-template>      
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="factor">
          <xsl:with-param name="var" select="$var"/>
          <xsl:with-param name="index" select="$index + 1"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template name="variable">
    <xsl:param name="iteration"/>
    <xsl:param name="index"/>
    <xsl:if test="$iteration &gt; 0">
      <polynomial>
        <variable>
          <xsl:value-of select="$index"/>
        </variable>
      </polynomial>
      <xsl:call-template name="variable">
        <xsl:with-param name="iteration" select="$iteration - 1"/>
        <xsl:with-param name="index" select="$index"/>
      </xsl:call-template>
    </xsl:if>  
  </xsl:template>

  <!-- ****************************************************************************************
       **  Matrix Order
       **************************************************************************************** -->

  <xsl:template match="matrix-order">
    <xsl:param name="tuple-symbols"/>
    <interpretation>
      <type>
        <matrixInterpretation>
          <domain>
            <xsl:choose>
              <xsl:when test="@type='int'">
                <naturals/>
              </xsl:when>
              <xsl:when test="@type='arctic' and @belowZero='false'">
                <arctic/>
              </xsl:when>
              <xsl:otherwise>
                <arcticBelowZero/>
              </xsl:otherwise>
            </xsl:choose>
          </domain>
          <dimension>
            <xsl:value-of select="@dimension"/>
          </dimension>
          <strictDimension>1</strictDimension>
        </matrixInterpretation>
      </type> 
      <xsl:choose>
        <xsl:when test="@type='int'">
          <xsl:call-template name="matrix-mappings">
            <xsl:with-param name="order" select="."/>
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
            <xsl:with-param name="dimension" select="@dimension"/>
          </xsl:call-template>
        </xsl:when>
        <!-- <xsl:when test="@belowZero='true'">
          <xsl:call-template name="matrix-mappings">
            <xsl:with-param name="order" select="."/>
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
            <xsl:with-param name="dimension" select="@dimension"/>
            <xsl:with-param name="arctic" select="@type"/>
          </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
        </xsl:otherwise> -->
        <xsl:otherwise>
          <xsl:call-template name="matrix-mappings">
            <xsl:with-param name="order" select="."/>
            <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
            <xsl:with-param name="dimension" select="@dimension"/>
            <xsl:with-param name="arctic" select="@type"/>
          </xsl:call-template>
        </xsl:otherwise>
      </xsl:choose>
    </interpretation>
  </xsl:template>

  <xsl:template mode="nosharp" match="matrix-order">
    <xsl:param name="tuple-symbols"/>
    <interpretation>
      <type>
        <matrixInterpretation>
          <domain>
            <xsl:choose>
              <xsl:when test="@type='int'">
                <naturals/>
              </xsl:when>
              <xsl:when test="@type='arctic' and @belowZero='false'">
                <arctic/>
              </xsl:when>
              <xsl:otherwise>
                <arcticBelowZero/>
              </xsl:otherwise>
            </xsl:choose>
          </domain>
          <dimension>
            <xsl:value-of select="@dimension"/>
          </dimension>
          <strictDimension>1</strictDimension>
        </matrixInterpretation>
      </type>
      <xsl:choose>
        <xsl:when test="@type='int'">
          <xsl:call-template name="matrix-mappings-nosharp">
            <xsl:with-param name="order" select="."/>
            <xsl:with-param name="dimension" select="@dimension"/>
          </xsl:call-template>
        </xsl:when>
       <!-- <xsl:when test="@belowZero='true'">
          <xsl:call-template name="matrix-mappings-nosharp">
            <xsl:with-param name="order" select="."/>
            <xsl:with-param name="dimension" select="@dimension"/>
            <xsl:with-param name="arctic" select="@type"/>
          </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
        </xsl:otherwise>-->
        <xsl:otherwise>
          <xsl:call-template name="matrix-mappings-nosharp">
            <xsl:with-param name="order" select="."/>
            <xsl:with-param name="dimension" select="@dimension"/>
            <xsl:with-param name="arctic" select="@type"/>
          </xsl:call-template>
        </xsl:otherwise>
      </xsl:choose>
    </interpretation>
  </xsl:template>

  <xsl:template name="matrix-mappings">
    <xsl:param name="order"/>
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="i" select="1"/>
    <xsl:param name="dimension"/>
    <xsl:param name="arctic" select="false"/>
    <xsl:apply-templates select="$order/matrix-interpretation[$i]">
      <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      <xsl:with-param name="dimension" select="$dimension"/>
      <xsl:with-param name="arctic" select="$arctic"/>
    </xsl:apply-templates>
    <xsl:choose>
      <xsl:when test="$i &lt; count($order/matrix-interpretation)">
        <xsl:call-template name="matrix-mappings">
          <xsl:with-param name="order" select="$order"/>
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          <xsl:with-param name="i" select="$i + 1"/>
          <xsl:with-param name="dimension" select="$dimension"/>
          <xsl:with-param name="arctic" select="$arctic"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="matrix-mappings-nosharp">
    <xsl:param name="order"/>
    <xsl:param name="i" select="1"/>
    <xsl:param name="dimension"/>
    <xsl:param name="arctic" select="false"/>
    <xsl:apply-templates mode="nosharp" select="$order/matrix-interpretation[$i]">
      <xsl:with-param name="dimension" select="$dimension"/>
      <xsl:with-param name="arctic" select="$arctic"/>
    </xsl:apply-templates>
    <xsl:choose>
      <xsl:when test="$i &lt; count($order/matrix-interpretation)">
        <xsl:call-template name="matrix-mappings-nosharp">
          <xsl:with-param name="order" select="$order"/>
          <xsl:with-param name="i" select="$i + 1"/>
          <xsl:with-param name="dimension" select="$dimension"/>
          <xsl:with-param name="arctic" select="$arctic"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="matrix-interpretation">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="dimension"/>
    <xsl:param name="arctic"/>
    <interpret>
      <xsl:apply-templates select="symbol">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        <xsl:with-param name="dimension" select="$dimension"/>
      </xsl:apply-templates>
      <xsl:apply-templates select="mpolynomial">
        <xsl:with-param name="dimension" select="$dimension"/>
        <xsl:with-param name="arctic" select="$arctic"/>
      </xsl:apply-templates>
    </interpret>
  </xsl:template>

  <xsl:template mode="nosharp" match="matrix-interpretation">
    <xsl:param name="dimension"/>
    <xsl:param name="arctic"/>
    <interpret>
      <xsl:apply-templates mode="nosharp" select="symbol">
        <xsl:with-param name="dimension" select="$dimension"/>
      </xsl:apply-templates>
      <xsl:apply-templates select="mpolynomial">
        <xsl:with-param name="dimension" select="$dimension"/>
        <xsl:with-param name="arctic" select="$arctic"/>
      </xsl:apply-templates>
    </interpret>
  </xsl:template>

  <xsl:template match="mpolynomial">
    <xsl:param name="dimension"/>
    <xsl:param name="arctic"/>
    <arity>
      <xsl:choose>
        <xsl:when test="count(../labeledSymbol) = 0">
          <xsl:value-of select="../symbol/@arity"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="../labeledSymbol/symbol/@arity"/>
        </xsl:otherwise>
      </xsl:choose>
    </arity>
    <polynomial>
      <sum>
        <xsl:choose>
          <xsl:when test="count(mmonomial)=0">
            <polynomial>
              <coefficient>
                <integer>0</integer>
              </coefficient>
            </polynomial>
          </xsl:when>
          <xsl:otherwise>
            <xsl:apply-templates select="mmonomial">
              <xsl:with-param name="dimension" select="$dimension"/>
              <xsl:with-param name="arctic" select="$arctic"/>
            </xsl:apply-templates>
          </xsl:otherwise>
        </xsl:choose>
      </sum>
    </polynomial>
  </xsl:template>

  <xsl:template match="mmonomial">
    <xsl:param name="dimension"/>
    <xsl:param name="arctic"/>
    <polynomial>
      <product>
        <polynomial>
          <xsl:choose>
            <xsl:when test="count(polo-factor) &gt; 0">
              <coefficient>
                <xsl:apply-templates select="matrix">
                  <xsl:with-param name="dimension" select="$dimension"/>
                  <xsl:with-param name="arctic" select="$arctic"/>
                </xsl:apply-templates>
              </coefficient>
            </xsl:when>
            <xsl:otherwise>
              <coefficient>
                <xsl:apply-templates select="matrix/mvect">
                  <xsl:with-param name="dimension" select="$dimension"/>
                  <xsl:with-param name="arctic" select="$arctic"/>
                </xsl:apply-templates>
              </coefficient>
            </xsl:otherwise>
          </xsl:choose>
        </polynomial>
        <xsl:if test="count(polo-factor) &gt; 0">
          <xsl:call-template name="polo-factors">
            <xsl:with-param name="monom" select="."/>
          </xsl:call-template>
        </xsl:if>
      </product>
    </polynomial>
  </xsl:template>
        
  <xsl:template match="matrix">
    <xsl:param name="dimension"/>
    <xsl:param name="arctic"/>
    <matrix>
      <xsl:apply-templates select="mvect">
        <xsl:with-param name="dimension" select="$dimension"/>
        <xsl:with-param name="arctic" select="$arctic"/>
      </xsl:apply-templates>  
    </matrix>
  </xsl:template>

  <xsl:template match="mvect">
    <xsl:param name="dimension"/>
    <xsl:param name="arctic"/>
    <vector>
      <xsl:choose>
        <xsl:when test="count(integer) &gt; count(arctic-int)">
          <xsl:call-template name="vectorList">
            <xsl:with-param name="node" select="."/>
            <xsl:with-param name="stop" select="count(integer)"/>
            <xsl:with-param name="dimension" select="$dimension"/>
            <xsl:with-param name="arctic" select="$arctic"/>
          </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
          <xsl:call-template name="vectorList">
            <xsl:with-param name="node" select="."/>
            <xsl:with-param name="stop" select="count(arctic-int)"/>
            <xsl:with-param name="dimension" select="$dimension"/>
            <xsl:with-param name="arctic" select="$arctic"/>
          </xsl:call-template>
        </xsl:otherwise>
      </xsl:choose>
    </vector>
  </xsl:template>

  <xsl:template name="vectorList">
    <xsl:param name="dimension"/>
    <xsl:param name="node"/>
    <xsl:param name="start" select="1"/>
    <xsl:param name="stop"/>
    <xsl:param name="arctic"/>
    <xsl:choose>
      <xsl:when test="$start &gt; $stop">
        <!-- Fill collapsing matrices with zeros -->
        <xsl:choose>
          <xsl:when test="number($dimension) &gt; $stop">
            <xsl:call-template name="fillVector">
              <xsl:with-param name="dimension" select="$dimension"/>
              <xsl:with-param name="stop" select="$stop"/>
              <xsl:with-param name="arctic" select="$arctic"/>
            </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <xsl:text/>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
      <xsl:otherwise>
        <coefficient>
          <xsl:choose>
            <xsl:when test="count($node/arctic-int) &gt; 0">
              <xsl:choose>
                <xsl:when test="$node/arctic-int[$start]/@infinite = 'true'">
                  <minusInfinity/>
                </xsl:when>
                <xsl:otherwise>
                  <integer>
                    <xsl:value-of select="$node/arctic-int[$start]/@value"/>
                  </integer>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:when>
            <xsl:otherwise>
              <integer>
                <xsl:value-of select="$node/integer[$start]/@value"/>
              </integer>
            </xsl:otherwise>
          </xsl:choose>
        </coefficient>
        <xsl:call-template name="vectorList">
          <xsl:with-param name="node" select="$node"/>
          <xsl:with-param name="start" select="$start+1"/>
          <xsl:with-param name="stop" select="$stop"/>
          <xsl:with-param name="dimension" select="$dimension"/>
          <xsl:with-param name="arctic" select="$arctic"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>
  
  <xsl:template name="fillVector">
    <xsl:param name="dimension"/>
    <xsl:param name="stop"/>
    <xsl:param name="arctic"/>
    <coefficient>
      <xsl:choose>
        <xsl:when test="$arctic='arctic'">
          <minusInfinity/>
        </xsl:when>
        <xsl:otherwise>
          <integer>0</integer>
        </xsl:otherwise>
      </xsl:choose>
    </coefficient>
    <xsl:if test="$dimension &gt; ($stop + 1)">
      <xsl:call-template name="fillVector">
        <xsl:with-param name="dimension" select="$dimension"/>
        <xsl:with-param name="stop" select="$stop + 1"/>
        <xsl:with-param name="arctic" select="$arctic"/>
      </xsl:call-template>
    </xsl:if>
  </xsl:template>
  
  <!-- ****************************************************************************************
       **  Term-related structures
       **************************************************************************************** -->

  <xsl:template match="labeledSymbol">
    <xsl:param name="tuple-symbols"/>
    <labeledSymbol>
     <!-- This is an exclusive or -->
     <xsl:apply-templates select="symbol">
       <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
     </xsl:apply-templates>
     <xsl:apply-templates select="labeledSymbol">
       <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
  	  </xsl:apply-templates>

  	  <xsl:apply-templates select="label">
  	    <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
  	  </xsl:apply-templates>
  	</labeledSymbol>
  </xsl:template>

  <xsl:template mode="nosharp" match="labeledSymbol">
    <labeledSymbol>
  	  <!-- This is an exclusive or -->
  	  <xsl:apply-templates mode="nosharp" select="symbol"/>
  	  <xsl:apply-templates mode="nosharp" select="labeledSymbol"/>

  	  <xsl:apply-templates mode="nosharp" select="label"/>
  	</labeledSymbol>
  </xsl:template>

  <xsl:template match="label">
    <xsl:param name="tuple-symbols"/>
    <xsl:choose>
      <xsl:when test="@type = 'FSym'">
        <symbolLabel>
          <xsl:choose>
            <xsl:when test="count(integer) = 0">
              <!-- This is an exclusive or -->
              <xsl:apply-templates mode="nosharp" select="symbol"/>
              <xsl:apply-templates mode="nosharp" select="labeledSymbol"/>
            </xsl:when>
            <xsl:otherwise>
              <number>
		        <xsl:apply-templates/>
              </number>
            </xsl:otherwise>
          </xsl:choose>
        </symbolLabel>
      </xsl:when>
      <xsl:otherwise>
        <numberLabel>
          <xsl:choose>
            <xsl:when test="count(integer) = 0">
              <!-- This is an exclusive or -->
              <xsl:apply-templates mode="nosharp" select="symbol"/>
              <xsl:apply-templates mode="nosharp" select="labeledSymbol"/>
            </xsl:when>
            <xsl:otherwise>
              <number>
		        <xsl:apply-templates/>
              </number>
            </xsl:otherwise>
          </xsl:choose>
        </numberLabel>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template mode="nosharp" match="label">
    <xsl:choose>
      <xsl:when test="@type = 'FSym'">
        <symbolLabel>
          <xsl:choose>
            <xsl:when test="count(integer) = 0">
              <!-- This is an exclusive or -->
  	          <xsl:apply-templates mode="nosharp" select="symbol"/>
              <xsl:apply-templates mode="nosharp" select="labeledSymbol"/>
            </xsl:when>
            <xsl:otherwise>
              <number>
		        <xsl:apply-templates/>
              </number>
            </xsl:otherwise>
          </xsl:choose>
        </symbolLabel>
      </xsl:when>
      <xsl:otherwise>
        <numberLabel>
          <xsl:choose>
            <xsl:when test="count(integer) = 0">
              <!-- This is an exclusive or -->
  	          <xsl:apply-templates mode="nosharp" select="symbol"/>
              <xsl:apply-templates mode="nosharp" select="labeledSymbol"/>
            </xsl:when>
            <xsl:otherwise>
              <number>
		        <xsl:apply-templates/>
              </number>
            </xsl:otherwise>
          </xsl:choose>
        </numberLabel>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- Tuple symbols must have the same identifier as the function symbols they
       are derived from. -->
  <xsl:template match="symbol">
    <xsl:param name="tuple-symbols"/>
    <xsl:variable name="ar" select="@arity"/>
    <xsl:variable name="na" select="@name"/>
    <xsl:choose>
      <!-- use exslt:node-set to query generated node of tuple-symbols -->
      <xsl:when test="count(exslt:node-set($tuple-symbols)/defined-to-tuple/entry/tupled/symbol[@name = $na and @arity = $ar]) = 0">
        <name>
          <xsl:value-of select="@name"/>
        </name>
        <!--
        <arity>
          <xsl:value-of select="@arity"/>
        </arty>
        -->
      </xsl:when>
      <xsl:otherwise>
        <sharp>
          <name>
            <xsl:value-of select="exslt:node-set($tuple-symbols)/defined-to-tuple/entry[count(tupled/symbol[@name = $na and @arity = $ar]) > 0]/orig/symbol/@name"/>
          </name>
          <!--
          <arity>
            <xsl:value-of select="exslt:node-set($tuple-symbols)/defined-to-tuple/entry[count(tupled/symbol[@name = $na and @arity = $ar]) > 0]/orig/symbol/@arity"/>
          </arity>
          -->
        </sharp>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template mode="nosharp" match="symbol">
    <name>
      <xsl:value-of select="@name"/>
    </name>
    <!--
    <arity>
      <xsl:value-of select="@arity"/>
    </arity>
    -->
  </xsl:template>

  <xsl:template match="variable">
    <xsl:param name="tuple-symbols"/>
    <var>
      <xsl:value-of select="@name"/>
    </var>
  </xsl:template>

  <xsl:template mode="nosharp" match="variable">
    <var>
      <xsl:value-of select="@name"/>
    </var>
  </xsl:template>

  <xsl:template match="term">
    <xsl:param name="tuple-symbols"/>
    <xsl:apply-templates>
      <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
    </xsl:apply-templates>
  </xsl:template>

  <xsl:template mode="nosharp" match="term">
    <xsl:apply-templates mode="nosharp"/>
  </xsl:template>

  <xsl:template match="fun-app">
    <xsl:param name="tuple-symbols"/>
    <funapp>
      <xsl:apply-templates select="symbol">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
      <xsl:apply-templates select="labeledSymbol">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:apply-templates>
      <xsl:call-template name="arg-list">
        <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
      </xsl:call-template>
    </funapp>
  </xsl:template>

  <xsl:template mode="nosharp" match="fun-app">
    <funapp>
      <xsl:apply-templates mode="nosharp" select="symbol"/>
      <xsl:apply-templates mode="nosharp" select="labeledSymbol"/>
      <xsl:call-template name="arg-list-nosharp"/>
    </funapp>
  </xsl:template>

  <xsl:template name="arg-list">
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="i" select="1"/>
    <xsl:if test="$i &lt;= count(term)">
      <arg>
        <xsl:apply-templates select="term[$i]">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        </xsl:apply-templates>
      </arg>
    </xsl:if>
    <xsl:choose>
      <xsl:when test="$i &lt; count(term)">
        <xsl:call-template name="arg-list">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          <xsl:with-param name="i" select="$i + 1"/>
        </xsl:call-template>
      </xsl:when>
      <!--No more arguments left-->
      <xsl:otherwise><xsl:text/></xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- A duplicated version of term and its dependencies for scenarios
       where tuple-symbols is not present (such as non-termination
       proofs, which operate on TRSs rather than QDPs)
-->

  <xsl:template name="arg-list-nosharp">
    <xsl:param name="i" select="1"/>
    <xsl:if test="$i &lt;= count(term)">
      <arg>
        <xsl:apply-templates mode="nosharp" select="term[$i]"/>
      </arg>
    </xsl:if>
    <xsl:choose>
      <xsl:when test="$i &lt; count(term)">
        <xsl:call-template name="arg-list-nosharp">
          <xsl:with-param name="i" select="$i + 1"/>
        </xsl:call-template>
      </xsl:when>
      <!--No more arguments left-->
      <xsl:otherwise><xsl:text/></xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- Rules -->

  <xsl:template match="rule">
    <xsl:param name="tuple-symbols"/>
    <rule>
      <lhs>
        <xsl:apply-templates select="term[1]">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        </xsl:apply-templates>
      </lhs>
      <rhs>
        <xsl:apply-templates select="term[2]">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        </xsl:apply-templates>
      </rhs>
    </rule>
  </xsl:template>

  <xsl:template name="ruleset">
    <xsl:param name="rules"/>
    <xsl:param name="tuple-symbols"/>
    <xsl:param name="i" select="1"/>
    <xsl:choose>
      <xsl:when test="$i &lt;= count($rules/rule)">
        <xsl:apply-templates select="$rules/rule[$i]">
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        </xsl:apply-templates>
      </xsl:when>
    </xsl:choose>
    <xsl:choose>
      <xsl:when test="$i &lt; count($rules/rule)">
        <xsl:call-template name="ruleset">
          <xsl:with-param name="rules" select="$rules"/>
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
          <xsl:with-param name="i" select="$i + 1"/>
        </xsl:call-template>
      </xsl:when>
      <!--  No more rules left -->
      <xsl:otherwise><xsl:text/></xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template mode="nosharp" match="rule">
    <rule>
      <lhs>
        <xsl:apply-templates mode="nosharp" select="term[1]"/>
      </lhs>
      <rhs>
        <xsl:apply-templates mode="nosharp" select="term[2]"/>
      </rhs>
    </rule>
  </xsl:template>

  <xsl:template name="ruleset-nosharp">
    <xsl:param name="rules"/>
    <xsl:param name="i" select="1"/>
    <xsl:choose>
      <xsl:when test="$i &lt;= count($rules/rule)">
        <xsl:apply-templates mode="nosharp" select="$rules/rule[$i]"/>
      </xsl:when>
    </xsl:choose>
    <xsl:choose>
      <xsl:when test="$i &lt; count($rules/rule)">
        <xsl:call-template name="ruleset-nosharp">
          <xsl:with-param name="rules" select="$rules"/>
          <xsl:with-param name="i" select="$i + 1"/>
        </xsl:call-template>
      </xsl:when>
      <!--  No more rules left -->
      <xsl:otherwise><xsl:text/></xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- A convenience template which just wraps <trs> around a ruleset -->
  <xsl:template match="trs">
    <xsl:param name="tuple-symbols"/>
      <rules>
        <xsl:call-template name="ruleset">
          <xsl:with-param name="rules" select="."/>
          <xsl:with-param name="tuple-symbols" select="$tuple-symbols"/>
        </xsl:call-template>
      </rules>
  </xsl:template>

  <xsl:template mode="nosharp" match="trs">
      <rules>
        <xsl:call-template name="ruleset-nosharp">
          <xsl:with-param name="rules" select="."/>
        </xsl:call-template>
      </rules>
  </xsl:template>

  <!-- ****************************************************************************************
       **  Auxiliary functions
       **************************************************************************************** -->

  <!-- Transformation of natural numbers into CetaXML -->

  <xsl:template match="integer">
    <xsl:value-of select="@value"/>
  </xsl:template>

</xsl:transform>