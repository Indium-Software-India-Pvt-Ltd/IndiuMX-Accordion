import { Component, ReactNode, createElement } from "react";

import { AccordianContainerProps } from "../typings/AccordianProps";

import "./ui/Accordian.css";

import Accordion from "react-bootstrap/Accordion";

export class Accordian extends Component<AccordianContainerProps> {

    public header = this.props.heading?.value ? this.props.heading?.value : " ";
  

    handleEnter = ()=>{
        if (this.props.onEnter && this.props.onEnter.canExecute) {
            this.props.onEnter.execute();
        }
    }

    handleExit = ()=>{
        if (this.props.onExit && this.props.onExit.canExecute) {
            this.props.onExit.execute();
        }
    }

    handler = ()=>{
        if(this.props.boolean){
            if (this.props.onEnter && this.props.onEnter.canExecute) {
                this.props.onEnter.execute();
            }
            return "0";
        }else{
            return "";
        }
    }

    handledefaultopen : any =  this.handler;

    render(): ReactNode {
        this.header = this.props.heading?.value ? this.props.heading?.value : " ";

        return (
                <Accordion defaultActiveKey={this.handledefaultopen}>
                    <Accordion.Item eventKey="0">
                        <Accordion.Header className="AccordianHeader">{this.header}</Accordion.Header>
                        <Accordion.Body onEnter={this.handleEnter} onExit={this.handleExit}>
                            {this.props.content}
                        </Accordion.Body>
                    </Accordion.Item>
                </Accordion>
        );
    }
}
