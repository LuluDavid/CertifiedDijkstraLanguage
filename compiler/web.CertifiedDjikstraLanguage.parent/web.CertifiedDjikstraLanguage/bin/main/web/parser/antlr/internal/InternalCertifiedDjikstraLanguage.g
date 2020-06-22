/*
 * generated by Xtext 2.22.0
 */
grammar InternalCertifiedDjikstraLanguage;

options {
	superClass=AbstractInternalAntlrParser;
}

@lexer::header {
package web.parser.antlr.internal;

// Hack: Use our own Lexer superclass by means of import. 
// Currently there is no other way to specify the superclass for the lexer.
import org.eclipse.xtext.parser.antlr.Lexer;
}

@parser::header {
package web.parser.antlr.internal;

import org.eclipse.xtext.*;
import org.eclipse.xtext.parser.*;
import org.eclipse.xtext.parser.impl.*;
import org.eclipse.emf.ecore.util.EcoreUtil;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.parser.antlr.AbstractInternalAntlrParser;
import org.eclipse.xtext.parser.antlr.XtextTokenStream;
import org.eclipse.xtext.parser.antlr.XtextTokenStream.HiddenTokens;
import org.eclipse.xtext.parser.antlr.AntlrDatatypeRuleToken;
import web.services.CertifiedDjikstraLanguageGrammarAccess;

}

@parser::members {

 	private CertifiedDjikstraLanguageGrammarAccess grammarAccess;

    public InternalCertifiedDjikstraLanguageParser(TokenStream input, CertifiedDjikstraLanguageGrammarAccess grammarAccess) {
        this(input);
        this.grammarAccess = grammarAccess;
        registerRules(grammarAccess.getGrammar());
    }

    @Override
    protected String getFirstRuleName() {
    	return "Module";
   	}

   	@Override
   	protected CertifiedDjikstraLanguageGrammarAccess getGrammarAccess() {
   		return grammarAccess;
   	}

}

@rulecatch {
    catch (RecognitionException re) {
        recover(input,re);
        appendSkippedTokens();
    }
}

// Entry rule entryRuleModule
entryRuleModule returns [EObject current=null]@init {
	HiddenTokens myHiddenTokenState = ((XtextTokenStream)input).setHiddenTokens("RULE_WS", "RULE_ML_COMMENT", "RULE_SL_COMMENT");
}:
	{ newCompositeNode(grammarAccess.getModuleRule()); }
	iv_ruleModule=ruleModule
	{ $current=$iv_ruleModule.current; }
	EOF;
finally {
	myHiddenTokenState.restore();
}

// Rule Module
ruleModule returns [EObject current=null]
@init {
	enterRule();
	HiddenTokens myHiddenTokenState = ((XtextTokenStream)input).setHiddenTokens("RULE_WS", "RULE_ML_COMMENT", "RULE_SL_COMMENT");
}
@after {
	leaveRule();
}:
	(
		(
			{
				newCompositeNode(grammarAccess.getModuleAccess().getDeclarationsDocDeclarationParserRuleCall_0());
			}
			lv_declarations_0_0=ruleDocDeclaration
			{
				if ($current==null) {
					$current = createModelElementForParent(grammarAccess.getModuleRule());
				}
				add(
					$current,
					"declarations",
					lv_declarations_0_0,
					"web.CertifiedDjikstraLanguage.DocDeclaration");
				afterParserOrEnumRuleCall();
			}
		)
	)*
;
finally {
	myHiddenTokenState.restore();
}

// Entry rule entryRuleDocDeclaration
entryRuleDocDeclaration returns [EObject current=null]:
	{ newCompositeNode(grammarAccess.getDocDeclarationRule()); }
	iv_ruleDocDeclaration=ruleDocDeclaration
	{ $current=$iv_ruleDocDeclaration.current; }
	EOF;

// Rule DocDeclaration
ruleDocDeclaration returns [EObject current=null]
@init {
	enterRule();
}
@after {
	leaveRule();
}:
	(
		(
			(
				lv_doc_0_0=RULE_CDL_DOC
				{
					newLeafNode(lv_doc_0_0, grammarAccess.getDocDeclarationAccess().getDocCDL_DOCTerminalRuleCall_0_0());
				}
				{
					if ($current==null) {
						$current = createModelElement(grammarAccess.getDocDeclarationRule());
					}
					setWithLastConsumed(
						$current,
						"doc",
						lv_doc_0_0,
						"web.CertifiedDjikstraLanguage.CDL_DOC");
				}
			)
		)?
		(
			(
				{
					newCompositeNode(grammarAccess.getDocDeclarationAccess().getDeclarationDeclarationParserRuleCall_1_0());
				}
				lv_declaration_1_0=ruleDeclaration
				{
					if ($current==null) {
						$current = createModelElementForParent(grammarAccess.getDocDeclarationRule());
					}
					set(
						$current,
						"declaration",
						lv_declaration_1_0,
						"web.CertifiedDjikstraLanguage.Declaration");
					afterParserOrEnumRuleCall();
				}
			)
		)
	)
;

// Entry rule entryRuleDeclaration
entryRuleDeclaration returns [EObject current=null]:
	{ newCompositeNode(grammarAccess.getDeclarationRule()); }
	iv_ruleDeclaration=ruleDeclaration
	{ $current=$iv_ruleDeclaration.current; }
	EOF;

// Rule Declaration
ruleDeclaration returns [EObject current=null]
@init {
	enterRule();
}
@after {
	leaveRule();
}:
	(
		{
			newCompositeNode(grammarAccess.getDeclarationAccess().getInstantiationParserRuleCall_0());
		}
		this_Instantiation_0=ruleInstantiation
		{
			$current = $this_Instantiation_0.current;
			afterParserOrEnumRuleCall();
		}
		    |
		{
			newCompositeNode(grammarAccess.getDeclarationAccess().getTransformationParserRuleCall_1());
		}
		this_Transformation_1=ruleTransformation
		{
			$current = $this_Transformation_1.current;
			afterParserOrEnumRuleCall();
		}
	)
;

// Entry rule entryRuleTransformation
entryRuleTransformation returns [EObject current=null]:
	{ newCompositeNode(grammarAccess.getTransformationRule()); }
	iv_ruleTransformation=ruleTransformation
	{ $current=$iv_ruleTransformation.current; }
	EOF;

// Rule Transformation
ruleTransformation returns [EObject current=null]
@init {
	enterRule();
}
@after {
	leaveRule();
}:
	(
		otherlv_0='Transformation'
		{
			newLeafNode(otherlv_0, grammarAccess.getTransformationAccess().getTransformationKeyword_0());
		}
		(
			(
				{
					newCompositeNode(grammarAccess.getTransformationAccess().getBodyTransformationBodyParserRuleCall_1_0());
				}
				lv_body_1_0=ruleTransformationBody
				{
					if ($current==null) {
						$current = createModelElementForParent(grammarAccess.getTransformationRule());
					}
					set(
						$current,
						"body",
						lv_body_1_0,
						"web.CertifiedDjikstraLanguage.TransformationBody");
					afterParserOrEnumRuleCall();
				}
			)
		)
	)
;

// Entry rule entryRuleTransformationBody
entryRuleTransformationBody returns [EObject current=null]:
	{ newCompositeNode(grammarAccess.getTransformationBodyRule()); }
	iv_ruleTransformationBody=ruleTransformationBody
	{ $current=$iv_ruleTransformationBody.current; }
	EOF;

// Rule TransformationBody
ruleTransformationBody returns [EObject current=null]
@init {
	enterRule();
}
@after {
	leaveRule();
}:
	(
		otherlv_0='o->'
		{
			newLeafNode(otherlv_0, grammarAccess.getTransformationBodyAccess().getOKeyword_0());
		}
		(
			(
				{
					newCompositeNode(grammarAccess.getTransformationBodyAccess().getGraphGraphOrDeclParserRuleCall_1_0());
				}
				lv_graph_1_0=ruleGraphOrDecl
				{
					if ($current==null) {
						$current = createModelElementForParent(grammarAccess.getTransformationBodyRule());
					}
					set(
						$current,
						"graph",
						lv_graph_1_0,
						"web.CertifiedDjikstraLanguage.GraphOrDecl");
					afterParserOrEnumRuleCall();
				}
			)
		)
		otherlv_2=','
		{
			newLeafNode(otherlv_2, grammarAccess.getTransformationBodyAccess().getCommaKeyword_2());
		}
		(
			(
				{
					newCompositeNode(grammarAccess.getTransformationBodyAccess().getRootRootOrDeclParserRuleCall_3_0());
				}
				lv_root_3_0=ruleRootOrDecl
				{
					if ($current==null) {
						$current = createModelElementForParent(grammarAccess.getTransformationBodyRule());
					}
					set(
						$current,
						"root",
						lv_root_3_0,
						"web.CertifiedDjikstraLanguage.RootOrDecl");
					afterParserOrEnumRuleCall();
				}
			)
		)
	)
;

// Entry rule entryRuleGraphOrDecl
entryRuleGraphOrDecl returns [EObject current=null]:
	{ newCompositeNode(grammarAccess.getGraphOrDeclRule()); }
	iv_ruleGraphOrDecl=ruleGraphOrDecl
	{ $current=$iv_ruleGraphOrDecl.current; }
	EOF;

// Rule GraphOrDecl
ruleGraphOrDecl returns [EObject current=null]
@init {
	enterRule();
}
@after {
	leaveRule();
}:
	(
		(
			(
				{
					$current = forceCreateModelElement(
						grammarAccess.getGraphOrDeclAccess().getGraphDeclAction_0_0(),
						$current);
				}
			)
			(
				(
					{
						if ($current==null) {
							$current = createModelElement(grammarAccess.getGraphOrDeclRule());
						}
					}
					otherlv_1=RULE_ID
					{
						newLeafNode(otherlv_1, grammarAccess.getGraphOrDeclAccess().getGraphDeclGraphInstantiationCrossReference_0_1_0());
					}
				)
			)
		)
		    |
		(
			(
				{
					$current = forceCreateModelElement(
						grammarAccess.getGraphOrDeclAccess().getGraphAction_1_0(),
						$current);
				}
			)
			(
				(
					{
						newCompositeNode(grammarAccess.getGraphOrDeclAccess().getGraphGraphParserRuleCall_1_1_0());
					}
					lv_graph_3_0=ruleGraph
					{
						if ($current==null) {
							$current = createModelElementForParent(grammarAccess.getGraphOrDeclRule());
						}
						set(
							$current,
							"graph",
							lv_graph_3_0,
							"web.CertifiedDjikstraLanguage.Graph");
						afterParserOrEnumRuleCall();
					}
				)
			)
		)
	)
;

// Entry rule entryRuleRootOrDecl
entryRuleRootOrDecl returns [EObject current=null]:
	{ newCompositeNode(grammarAccess.getRootOrDeclRule()); }
	iv_ruleRootOrDecl=ruleRootOrDecl
	{ $current=$iv_ruleRootOrDecl.current; }
	EOF;

// Rule RootOrDecl
ruleRootOrDecl returns [EObject current=null]
@init {
	enterRule();
}
@after {
	leaveRule();
}:
	(
		(
			(
				{
					$current = forceCreateModelElement(
						grammarAccess.getRootOrDeclAccess().getRootDeclAction_0_0(),
						$current);
				}
			)
			(
				(
					{
						if ($current==null) {
							$current = createModelElement(grammarAccess.getRootOrDeclRule());
						}
					}
					otherlv_1=RULE_ID
					{
						newLeafNode(otherlv_1, grammarAccess.getRootOrDeclAccess().getRootDeclRootInstantiationCrossReference_0_1_0());
					}
				)
			)
		)
		    |
		(
			(
				{
					$current = forceCreateModelElement(
						grammarAccess.getRootOrDeclAccess().getRootAction_1_0(),
						$current);
				}
			)
			(
				(
					{
						newCompositeNode(grammarAccess.getRootOrDeclAccess().getRootRootParserRuleCall_1_1_0());
					}
					lv_root_3_0=ruleRoot
					{
						if ($current==null) {
							$current = createModelElementForParent(grammarAccess.getRootOrDeclRule());
						}
						set(
							$current,
							"root",
							lv_root_3_0,
							"web.CertifiedDjikstraLanguage.Root");
						afterParserOrEnumRuleCall();
					}
				)
			)
		)
	)
;

// Entry rule entryRuleInstantiation
entryRuleInstantiation returns [EObject current=null]:
	{ newCompositeNode(grammarAccess.getInstantiationRule()); }
	iv_ruleInstantiation=ruleInstantiation
	{ $current=$iv_ruleInstantiation.current; }
	EOF;

// Rule Instantiation
ruleInstantiation returns [EObject current=null]
@init {
	enterRule();
}
@after {
	leaveRule();
}:
	(
		{
			newCompositeNode(grammarAccess.getInstantiationAccess().getGraphInstantiationParserRuleCall_0());
		}
		this_GraphInstantiation_0=ruleGraphInstantiation
		{
			$current = $this_GraphInstantiation_0.current;
			afterParserOrEnumRuleCall();
		}
		    |
		{
			newCompositeNode(grammarAccess.getInstantiationAccess().getRootInstantiationParserRuleCall_1());
		}
		this_RootInstantiation_1=ruleRootInstantiation
		{
			$current = $this_RootInstantiation_1.current;
			afterParserOrEnumRuleCall();
		}
	)
;

// Entry rule entryRuleGraphInstantiation
entryRuleGraphInstantiation returns [EObject current=null]:
	{ newCompositeNode(grammarAccess.getGraphInstantiationRule()); }
	iv_ruleGraphInstantiation=ruleGraphInstantiation
	{ $current=$iv_ruleGraphInstantiation.current; }
	EOF;

// Rule GraphInstantiation
ruleGraphInstantiation returns [EObject current=null]
@init {
	enterRule();
}
@after {
	leaveRule();
}:
	(
		(
			(
				lv_name_0_0=RULE_ID
				{
					newLeafNode(lv_name_0_0, grammarAccess.getGraphInstantiationAccess().getNameIDTerminalRuleCall_0_0());
				}
				{
					if ($current==null) {
						$current = createModelElement(grammarAccess.getGraphInstantiationRule());
					}
					setWithLastConsumed(
						$current,
						"name",
						lv_name_0_0,
						"org.eclipse.xtext.common.Terminals.ID");
				}
			)
		)
		otherlv_1=':='
		{
			newLeafNode(otherlv_1, grammarAccess.getGraphInstantiationAccess().getColonEqualsSignKeyword_1());
		}
		(
			(
				{
					newCompositeNode(grammarAccess.getGraphInstantiationAccess().getGraphGraphParserRuleCall_2_0());
				}
				lv_graph_2_0=ruleGraph
				{
					if ($current==null) {
						$current = createModelElementForParent(grammarAccess.getGraphInstantiationRule());
					}
					set(
						$current,
						"graph",
						lv_graph_2_0,
						"web.CertifiedDjikstraLanguage.Graph");
					afterParserOrEnumRuleCall();
				}
			)
		)
	)
;

// Entry rule entryRuleRootInstantiation
entryRuleRootInstantiation returns [EObject current=null]:
	{ newCompositeNode(grammarAccess.getRootInstantiationRule()); }
	iv_ruleRootInstantiation=ruleRootInstantiation
	{ $current=$iv_ruleRootInstantiation.current; }
	EOF;

// Rule RootInstantiation
ruleRootInstantiation returns [EObject current=null]
@init {
	enterRule();
}
@after {
	leaveRule();
}:
	(
		(
			(
				lv_name_0_0=RULE_ID
				{
					newLeafNode(lv_name_0_0, grammarAccess.getRootInstantiationAccess().getNameIDTerminalRuleCall_0_0());
				}
				{
					if ($current==null) {
						$current = createModelElement(grammarAccess.getRootInstantiationRule());
					}
					setWithLastConsumed(
						$current,
						"name",
						lv_name_0_0,
						"org.eclipse.xtext.common.Terminals.ID");
				}
			)
		)
		otherlv_1=':='
		{
			newLeafNode(otherlv_1, grammarAccess.getRootInstantiationAccess().getColonEqualsSignKeyword_1());
		}
		(
			(
				{
					newCompositeNode(grammarAccess.getRootInstantiationAccess().getRootRootParserRuleCall_2_0());
				}
				lv_root_2_0=ruleRoot
				{
					if ($current==null) {
						$current = createModelElementForParent(grammarAccess.getRootInstantiationRule());
					}
					set(
						$current,
						"root",
						lv_root_2_0,
						"web.CertifiedDjikstraLanguage.Root");
					afterParserOrEnumRuleCall();
				}
			)
		)
	)
;

// Entry rule entryRuleRoot
entryRuleRoot returns [EObject current=null]:
	{ newCompositeNode(grammarAccess.getRootRule()); }
	iv_ruleRoot=ruleRoot
	{ $current=$iv_ruleRoot.current; }
	EOF;

// Rule Root
ruleRoot returns [EObject current=null]
@init {
	enterRule();
}
@after {
	leaveRule();
}:
	(
		otherlv_0='R'
		{
			newLeafNode(otherlv_0, grammarAccess.getRootAccess().getRKeyword_0());
		}
		(
			{
				$current = forceCreateModelElement(
					grammarAccess.getRootAccess().getRootAction_1(),
					$current);
			}
		)
		(
			(
				{
					newCompositeNode(grammarAccess.getRootAccess().getValVertexParserRuleCall_2_0());
				}
				lv_val_2_0=ruleVertex
				{
					if ($current==null) {
						$current = createModelElementForParent(grammarAccess.getRootRule());
					}
					set(
						$current,
						"val",
						lv_val_2_0,
						"web.CertifiedDjikstraLanguage.Vertex");
					afterParserOrEnumRuleCall();
				}
			)
		)
	)
;

// Entry rule entryRuleGraph
entryRuleGraph returns [EObject current=null]:
	{ newCompositeNode(grammarAccess.getGraphRule()); }
	iv_ruleGraph=ruleGraph
	{ $current=$iv_ruleGraph.current; }
	EOF;

// Rule Graph
ruleGraph returns [EObject current=null]
@init {
	enterRule();
}
@after {
	leaveRule();
}:
	(
		otherlv_0='G'
		{
			newLeafNode(otherlv_0, grammarAccess.getGraphAccess().getGKeyword_0());
		}
		(
			{
				$current = forceCreateModelElement(
					grammarAccess.getGraphAccess().getGraphAction_1(),
					$current);
			}
		)
		(
			(
				{
					newCompositeNode(grammarAccess.getGraphAccess().getArcsTripletParserRuleCall_2_0());
				}
				lv_arcs_2_0=ruleTriplet
				{
					if ($current==null) {
						$current = createModelElementForParent(grammarAccess.getGraphRule());
					}
					add(
						$current,
						"arcs",
						lv_arcs_2_0,
						"web.CertifiedDjikstraLanguage.Triplet");
					afterParserOrEnumRuleCall();
				}
			)
		)+
	)
;

// Entry rule entryRuleTriplet
entryRuleTriplet returns [EObject current=null]:
	{ newCompositeNode(grammarAccess.getTripletRule()); }
	iv_ruleTriplet=ruleTriplet
	{ $current=$iv_ruleTriplet.current; }
	EOF;

// Rule Triplet
ruleTriplet returns [EObject current=null]
@init {
	enterRule();
}
@after {
	leaveRule();
}:
	(
		(
			{
				$current = forceCreateModelElement(
					grammarAccess.getTripletAccess().getTripletAction_0(),
					$current);
			}
		)
		otherlv_1='('
		{
			newLeafNode(otherlv_1, grammarAccess.getTripletAccess().getLeftParenthesisKeyword_1());
		}
		(
			(
				{
					newCompositeNode(grammarAccess.getTripletAccess().getXVertexParserRuleCall_2_0());
				}
				lv_x_2_0=ruleVertex
				{
					if ($current==null) {
						$current = createModelElementForParent(grammarAccess.getTripletRule());
					}
					set(
						$current,
						"x",
						lv_x_2_0,
						"web.CertifiedDjikstraLanguage.Vertex");
					afterParserOrEnumRuleCall();
				}
			)
		)
		otherlv_3=','
		{
			newLeafNode(otherlv_3, grammarAccess.getTripletAccess().getCommaKeyword_3());
		}
		(
			(
				{
					newCompositeNode(grammarAccess.getTripletAccess().getYVertexParserRuleCall_4_0());
				}
				lv_y_4_0=ruleVertex
				{
					if ($current==null) {
						$current = createModelElementForParent(grammarAccess.getTripletRule());
					}
					set(
						$current,
						"y",
						lv_y_4_0,
						"web.CertifiedDjikstraLanguage.Vertex");
					afterParserOrEnumRuleCall();
				}
			)
		)
		otherlv_5=','
		{
			newLeafNode(otherlv_5, grammarAccess.getTripletAccess().getCommaKeyword_5());
		}
		(
			(
				{
					newCompositeNode(grammarAccess.getTripletAccess().getZVertexParserRuleCall_6_0());
				}
				lv_z_6_0=ruleVertex
				{
					if ($current==null) {
						$current = createModelElementForParent(grammarAccess.getTripletRule());
					}
					set(
						$current,
						"z",
						lv_z_6_0,
						"web.CertifiedDjikstraLanguage.Vertex");
					afterParserOrEnumRuleCall();
				}
			)
		)
		otherlv_7=')'
		{
			newLeafNode(otherlv_7, grammarAccess.getTripletAccess().getRightParenthesisKeyword_7());
		}
	)
;

// Entry rule entryRuleVertex
entryRuleVertex returns [EObject current=null]:
	{ newCompositeNode(grammarAccess.getVertexRule()); }
	iv_ruleVertex=ruleVertex
	{ $current=$iv_ruleVertex.current; }
	EOF;

// Rule Vertex
ruleVertex returns [EObject current=null]
@init {
	enterRule();
}
@after {
	leaveRule();
}:
	(
		(
			lv_value_0_0=RULE_INT
			{
				newLeafNode(lv_value_0_0, grammarAccess.getVertexAccess().getValueINTTerminalRuleCall_0());
			}
			{
				if ($current==null) {
					$current = createModelElement(grammarAccess.getVertexRule());
				}
				setWithLastConsumed(
					$current,
					"value",
					lv_value_0_0,
					"org.eclipse.xtext.common.Terminals.INT");
			}
		)
	)
;

RULE_CDL_DOC : '(**' ( options {greedy=false;} : . )*'*)';

RULE_ID : '^'? ('a'..'z'|'A'..'Z'|'_') ('a'..'z'|'A'..'Z'|'_'|'0'..'9')*;

RULE_INT : ('0'..'9')+;

RULE_STRING : ('"' ('\\' .|~(('\\'|'"')))* '"'|'\'' ('\\' .|~(('\\'|'\'')))* '\'');

RULE_ML_COMMENT : '/*' ( options {greedy=false;} : . )*'*/';

RULE_SL_COMMENT : '//' ~(('\n'|'\r'))* ('\r'? '\n')?;

RULE_WS : (' '|'\t'|'\r'|'\n')+;

RULE_ANY_OTHER : .;