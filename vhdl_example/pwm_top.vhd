library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity pwm_top is
    port (
	clk : in std_logic;
	duty : in unsigned(15 downto 0);
	o : out std_logic_vector(2 downto 0)
    );
end entity pwm_top;

architecture rtl of pwm_top is
  constant pwm_size : integer := 12;
begin

pwm0 : entity work.pwm
generic map(
	size => 8)
port map(
	clk => clk,
	duty => duty,
	o => o);
end architecture rtl;
