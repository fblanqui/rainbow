<?xml version="1.0" encoding="ISO-8859-1"?>

<!-- example of varyadic problem -->

<problem
   xmlns="urn:rainbow.problem.format"
   xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
   xsi:schemaLocation="urn:rainbow.problem.format http://color.inria.fr/problem.xsd">
  <trs>
    <algebra>
      <varyadic/>
    </algebra>
    <theory/>
    <strategy>
      <none/>
    </strategy>
    <le_rules/>
    <rules>
      <rule> <!-- plus zero v0 = v0 -->
	<lhs>
	  <app>
            <fun>plus</fun>
            <arg><app><fun>zero</fun></app></arg>
            <arg><var>0</var></arg>
	  </app>
	</lhs>
	<rhs>
	  <var>0</var>
	</rhs>
      </rule>
      <rule>
	<lhs> <!-- plus (succ v1) v0 = succ (plus v1 v0) -->
	  <app>
            <fun>plus</fun>
            <arg>
              <app>
		<fun>succ</fun>
		<arg><var>1</var></arg>
              </app>
            </arg>
            <arg><var>0</var></arg>
	  </app>
	</lhs>
	<rhs>
	  <app>
            <fun>succ</fun>
            <arg>
              <app>
		<fun>plus</fun>
		<arg><var>1</var></arg>
		<arg><var>0</var></arg>
              </app>
            </arg>
	  </app>
	</rhs>
      </rule>
    </rules>
  </trs>
</problem>
